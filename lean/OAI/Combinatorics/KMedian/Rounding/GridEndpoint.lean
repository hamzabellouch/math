import Mathlib
import OAI.Combinatorics.KMedian.Process.ProcessCompletion
import OAI.Combinatorics.KMedian.Process.RoundParameters

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype F] [Fintype J] [DecidableEq F] [DecidableEq J] [PseudoMetricSpace X] in
 theorem radius_le_cost (S : Finset (Copy (F := F) Δ)) (d : F → ℝ) {R g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (hd : ∀ f, 0 ≤ d f)
    (hmax : ∃ i ∈ S, R=d i.1) : R ≤ (Δ:ℝ)*PhysicalPotential.cost g (fun i => d i.1) S := by
  obtain ⟨i,hi,rfl⟩ := hmax
  have ht := point_cost_le hg (fun i _ => hd i.1) hi
  have ht' := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg Δ)
  have he : (Δ:ℝ)*(g*d i.1)=d i.1 := by
    calc
      _ = (g*(Δ:ℝ))*d i.1 := by ring
      _ = _ := by rw [hunit,one_mul]
  rwa [he] at ht'

theorem grid_complete_parameters {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1/2)
    (p : Parameters τ) (A : Finset (Copy (F := F) p.Δ))
    (S₀ : J → Finset (Copy (F := F) p.Δ))
    (location : F → X) (client : J → X) (R : J → ℝ)
    (hR : ∀ j, 0 ≤ R j) (hm : ∀ j, mass p.g (S₀ j)=1)
    (hd : ∀ j i, i ∈ S₀ j → dist (client j) (location i.1) ≤ R j)
    (hmax : ∀ j, ∃ i ∈ S₀ j, R j=dist (client j) (location i.1))
    (hA : 1 ≤ mass p.g A) (hS : ∀ j, S₀ j ⊆ A) :
    ∃ O : Finset F, ∃ a : J → F,
      (∀ j, a j ∈ O) ∧ (O.card:ℝ) ≤ mass p.g A+(p.T:ℝ)*(4/(p.g*p.b)) ∧
      (∑ j, dist (client j) (location (a j))) ≤
      (1+2/Real.exp 1+8*τ)*(∑ j, PhysicalPotential.cost p.g
        (fun i => dist (client j) (location i.1)) (S₀ j)) := by
  let fail := (p.T:ℝ)*(96*(p.Δ:ℝ)^2*p.b/((2*p.h*p.g)*p.φ^2*p.g))
  have hf : fail ≤ τ := p.failure
  have hf1 : fail < 1 := lt_of_le_of_lt hf (by linarith only [hτ1])
  obtain ⟨O,a,ha,hcount,hcost⟩ := exists_completed A S₀ location client R
    p.gpos p.gle p.unit p.hpos p.hle p.φpos p.φle p.bpos p.probability p.small p.survival
    p.count hR hm hd hmax hA hS p.T hf1
  refine ⟨O,a,ha,hcount,hcost.trans ?_⟩
  let V := fun j => PhysicalPotential.cost p.g (fun i => dist (client j) (location i.1)) (S₀ j)
  have hV : ∀ j, 0 ≤ V j := fun _ => cost_nonneg p.gpos.le (fun _ _ => dist_nonneg)
  have hRV : ∀ j, R j ≤ (p.Δ:ℝ)*V j := fun j => radius_le_cost (S₀ j) _ p.gpos.le p.unit
    (fun _ => dist_nonneg) (hmax j)
  let α := 1+2/Real.exp 1
  have hαpos : 0 < α := by dsimp only [α]; positivity
  have hα3 : α ≤ 3 := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    have hp : 2/Real.exp 1 ≤ 2 := (div_le_iff₀ (Real.exp_pos 1)).mpr (by linarith only [he])
    dsimp only [α]
    linarith only [hp]
  have hc : ∀ j,
      α*V j+(p.T:ℝ)*(p.h*p.g*V j+batchConstant p.Δ*p.h*(p.φ+p.h)*R j)+
        5*R j*Real.exp (-(p.T:ℝ)*p.h/2) ≤ (α+τ)*V j := by
    intro j
    have hr := mul_le_mul_of_nonneg_left (hRV j)
      (show 0 ≤ (p.T:ℝ)*batchConstant p.Δ*p.h*(p.φ+p.h)+
          5*Real.exp (-(p.T:ℝ)*p.h/2) by
        have := batchConstant_nonneg p.Δ
        have := p.hpos
        have := p.φpos
        positivity)
    have he := mul_le_mul_of_nonneg_right p.error (hV j)
    nlinarith only [hr,he]
  have hsum : (∑ j, (α*V j+(p.T:ℝ)*(p.h*p.g*V j+batchConstant p.Δ*p.h*(p.φ+p.h)*R j)+
        5*R j*Real.exp (-(p.T:ℝ)*p.h/2))) ≤ (α+τ)*(∑ j, V j) := by
    rw [mul_sum]
    exact sum_le_sum (fun j _ => hc j)
  have hfactor : α+τ ≤ (α+8*τ)*(1-fail) := by
    have hατ := mul_le_mul_of_nonneg_right hα3 hτ.le
    have hτ2 := mul_le_mul_of_nonneg_left hτ1 hτ.le
    have hbase : α+τ ≤ (α+8*τ)*(1-τ) := by nlinarith only [hατ,hτ2]
    exact hbase.trans (mul_le_mul_of_nonneg_left (by linarith only [hf]) (by positivity))
  apply (div_le_iff₀ (sub_pos.mpr hf1)).mpr
  change (∑ j, (α*V j+(p.T:ℝ)*(p.h*p.g*V j+batchConstant p.Δ*p.h*(p.φ+p.h)*R j)+
      5*R j*Real.exp (-(p.T:ℝ)*p.h/2))) ≤ (α+8*τ)*(∑ j, V j)*(1-fail)
  exact hsum.trans ((mul_le_mul_of_nonneg_right hfactor (sum_nonneg (fun j _ => hV j))).trans_eq (by ring))

end MetricKMedian.CopyState
end
end

end OAI
