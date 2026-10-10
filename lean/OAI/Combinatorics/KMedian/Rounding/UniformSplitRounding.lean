import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationGrid

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset FixedBatch

theorem uniform_split_rounding {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℕ, ∀ (I J X : Type) [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] [Nonempty J] [PseudoMetricSpace X],
      ∀ (Fj : J → Finset I) (y : I → ℝ) (client : J → X) (location : I → X) (v : J → ℝ),
        (∀ a, 0 < y a) → (∀ a, y a ≤ 1) →
        (∀ c, ∑ a ∈ Fj c, y a=1) →
        (∀ c, ∑ a ∈ Fj c, y a*dist (client c) (location a)=v c) →
        (∀ c, ∀ a ∈ Fj c, ∀ b ∉ Fj c, dist (client c) (location a) ≤ dist (client c) (location b)) →
        ∃ O : Finset I, ∃ a : J → I,
          (∀ c, a c ∈ O) ∧ O.Nonempty ∧ (O.card:ℝ) ≤ (∑ a, y a)+(C:ℝ) ∧
          (∑ c, dist (client c) (location (a c))) ≤ (1+2/Real.exp 1+ε)*(∑ c, v c) := by
  let τ := min (ε/32) (1/2)
  have hτ : 0 < τ := lt_min (by positivity) (by norm_num)
  have hτ1 : τ ≤ 1/2 := min_le_right _ _
  have hτε : τ ≤ ε/32 := min_le_left _ _
  obtain ⟨δ,M,T₁,γ,hδ,hδ1,hM,hT,hγ,hγ1,hθ,hα,g₀,hg₀,hgrid⟩ := exists_preparation_parameters hτ
  obtain ⟨D₀,hD₀⟩ := all_fine_grids hg₀
  obtain ⟨p,hD,heven⟩ := exists_parameters hτ D₀
  have hpg : p.g=1/(p.Δ:ℝ) := by
    apply (eq_div_iff (show (p.Δ:ℝ) ≠ 0 by exact_mod_cast p.Δpos.ne')).mpr
    exact p.unit
  have hsmallg : p.g ≤ g₀ := by rw [hpg]; exact (hD₀ p.Δ hD).2.2
  obtain ⟨hfail,hfactor⟩ := hgrid p.g p.gpos hsmallg
  let C := ⌈3*p.g+(p.T:ℝ)*(4/(p.g*p.b))⌉₊
  refine ⟨C,?_⟩
  intro I J X _ _ _ _ _ _ Fj y client location v hy hy1 hunit hcost hnearest
  obtain ⟨O,a,ha,hO,hcount,hconn⟩ := split_solution_rounding Fj y client location v p hτ hτ1 hy hy1
    hM hδ hδ1 hT hθ hα hγ hγ1 heven (hfail.trans (by norm_num)) hunit hcost hnearest
  refine ⟨O,a,ha,hO,?_,hconn.trans ?_⟩
  · apply hcount.trans
    have hc : 3*p.g+(p.T:ℝ)*(4/(p.g*p.b)) ≤ (C:ℝ) := Nat.le_ceil _
    linarith only [hc]
  · have hV : 0 ≤ ∑ c, v c := sum_nonneg (fun c _ =>
      (sum_nonneg (fun a _ => mul_nonneg (hy a).le dist_nonneg)).trans_eq (hcost c))
    apply mul_le_mul_of_nonneg_right _ hV
    have hα3 : 1+2/Real.exp 1 ≤ 3 := by
      have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
      have hdiv : 2/Real.exp 1 ≤ 2 := (div_le_iff₀ (Real.exp_pos 1)).mpr (by linarith only [he])
      linarith only [hdiv]
    calc
      _ ≤ (1+2/Real.exp 1+8*τ)*(1+τ) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ ≤ 1+2/Real.exp 1+ε := by
        have ha := mul_le_mul_of_nonneg_right hα3 hτ.le
        have ht := mul_le_mul_of_nonneg_left hτ1 hτ.le
        nlinarith only [ha,ht,hτε,hε.le]

end MetricKMedian.Preparation
end
end

end OAI
