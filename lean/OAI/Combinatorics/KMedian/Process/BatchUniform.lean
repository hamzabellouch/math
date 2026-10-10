import Mathlib
import OAI.Combinatorics.KMedian.Process.ActualActions
import OAI.Combinatorics.KMedian.Process.FullBatchBound
import OAI.Combinatorics.KMedian.Process.ForcedTransition

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic

noncomputable def batchConstant (Δ : ℕ) : ℝ :=
  let n : ℝ := Δ^2+Δ
  16*n*(Δ:ℝ)^2+256*n^2+16*n+6

 theorem batchConstant_nonneg (Δ : ℕ) : 0 ≤ batchConstant Δ := by
  unfold batchConstant
  positivity

theorem uniform_remainder (Δ n o : ℕ) {h g φ R : ℝ}
    (hn : n ≤ Δ^2+Δ) (ho : o ≤ n^2)
    (hh : 0 ≤ h) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hφ : 0 ≤ φ) (hR : 0 ≤ R) :
    R*(16*(n:ℝ)*((Δ^2:ℕ):ℝ)*h^2*g^2+8*(n:ℝ)*φ*h*g+
      256*(o:ℝ)*h^2*g^2+6*h^2+8*(n:ℝ)*h^2*g) ≤
      batchConstant Δ*h*(φ+h)*R := by
  let N : ℝ := Δ^2+Δ
  have hn' : (n:ℝ) ≤ N := by dsimp only [N]; exact_mod_cast hn
  have ho' : (o:ℝ) ≤ N^2 := by
    have h := ho.trans (Nat.pow_le_pow_left hn 2)
    dsimp only [N]
    exact_mod_cast h
  have hn0 : 0 ≤ N := by dsimp [N]; positivity
  have hg2 : g^2 ≤ 1 := by nlinarith only [hg0,hg1]
  have t1 : 16*(n:ℝ)*((Δ^2:ℕ):ℝ)*h^2*g^2 ≤ 16*N*(Δ:ℝ)^2*h^2 := by
    have a : 16*(n:ℝ)*((Δ^2:ℕ):ℝ)*h^2 ≤ 16*N*(Δ:ℝ)^2*h^2 := by
      rw [Nat.cast_pow]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn' (by norm_num)) (sq_nonneg (Δ:ℝ))) (sq_nonneg h)
    exact (mul_le_of_le_one_right (by positivity) hg2).trans a
  have t2 : 8*(n:ℝ)*φ*h*g ≤ 8*N*φ*h := by
    exact (mul_le_of_le_one_right (by positivity) hg1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn' (by norm_num)) hφ) hh)
  have t3 : 256*(o:ℝ)*h^2*g^2 ≤ 256*N^2*h^2 := by
    exact (mul_le_of_le_one_right (by positivity) hg2).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ho' (by norm_num)) (sq_nonneg h))
  have t4 : 8*(n:ℝ)*h^2*g ≤ 8*N*h^2 := by
    exact (mul_le_of_le_one_right (by positivity) hg1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn' (by norm_num)) (sq_nonneg h))
  have hrem : 0 ≤ (16*N*(Δ:ℝ)^2+256*N^2+8*N+6)*φ*h+8*N*h^2 := by positivity
  have hs : 16*(n:ℝ)*((Δ^2:ℕ):ℝ)*h^2*g^2+8*(n:ℝ)*φ*h*g+
      256*(o:ℝ)*h^2*g^2+6*h^2+8*(n:ℝ)*h^2*g ≤ batchConstant Δ*h*(φ+h) := by
    change _ ≤ (16*N*(Δ:ℝ)^2+256*N^2+16*N+6)*h*(φ+h)
    nlinarith only [t1,t2,t3,t4,hrem]
  nlinarith only [mul_le_mul_of_nonneg_left hs hR]

variable {I : Type*} [DecidableEq I] [Fintype I]

theorem actual_batch_bound (G : I → Finset I) (H S S₀ F : Finset I) (Δ : ℕ)
    (q : HeavyAction (graphActions G) H → ℝ) {x g h φ R b b' : ℝ} (d : I → ℝ)
    (hG : ∀ i, (G i).card=Δ) (hg : 0 < g) (hg1 : g ≤ 1) (hunit : g*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hp1 : 2*h*g ≤ 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hq : ∀ e, 2*h*g ≤ q e ∧ q e ≤ (1+φ)*(2*h*g))
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hS : S ⊆ S₀) (h0 : mass g S₀=1) (hF : F ⊆ S) (hHS : H ∩ S ⊆ F)
    (hd0 : ∀ i, 0 ≤ d i) (hR : ∃ i ∈ S₀, R=d i) (hdR : ∀ i ∈ S₀, d i ≤ R)
    (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) (hb'0 : 0 ≤ b') (hb' : b' ≤ b)
    (hbF : ∀ i ∈ F, b' ≤ d i) (hbH : ∀ i ∈ H, b' ≤ d i) :
    let D := heavyActions (graphActions G) H
    let μ := PhysicalBatchLaw.law (balancedActions D Δ) (balancedConflicts D Δ)
      (2*h*g) q (by positivity) hp1 hq0 hq1
    μ.expect (fun A => potential (x*Real.exp (-h)) g d
      (nextAliveAt D (coefficient x (mass g S)) d (S \ F) A)
      (nextCap D d b' A)-potential x g d S b) ≤
      h*(timeRate x (mass g S)*PhysicalPotential.cost g d S+
        g*(∑ e ∈ relevant (graphActions G) S, charge (graphActions G) x g b d S e))+
      batchConstant Δ*h*(φ+h)*R := by
  intro D μ
  have hy : mass g S ≤ 1 := (mass_mono hg.le hS).trans_eq h0
  have hcard : S.card ≤ Δ := card_le_grid hg hunit S hy
  have hin : ∀ i, (FiniteGraph.incoming D.erase i).card ≤ Δ :=
    fun i => le_of_eq ((heavy_incoming_card G H i).trans (hG i))
  have hD := heavy_relevant_bound G H S hcard hG
  have hFull := full_relevant_bound G S hcard hG
  have hR0 : 0 ≤ R := by obtain ⟨i,_,rfl⟩ := hR; exact hd0 i
  have hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g := by
    intro e _
    have hpQ : 2*h*g ≤ 4*h*g := by nlinarith only [mul_nonneg hh0 hg.le]
    have hqQ : ∀ e, q e ≤ 4*h*g := by
      intro e
      have he := mul_le_mul_of_nonneg_right hφ1 (show 0 ≤ 2*h*g by positivity)
      linarith only [he,(hq e).2]
    have he := PhysicalBatchLaw.marginal_le (balancedActions D Δ) (balancedConflicts D Δ)
      (2*h*g) q (by positivity) hp1 hq0 hq1 (balancedConflicts_self D Δ) hpQ hqQ e
    change μ.prob _ ≤ _ at he
    linarith only [he]
  by_cases hFn : F.Nonempty
  · have hδ : g ≤ mass g F := by
      unfold mass
      have hf : (1:ℝ) ≤ F.card := by exact_mod_cast hFn.card_pos
      nlinarith only [mul_le_mul_of_nonneg_left hf hg.le]
    have hh := forced_step_bound D (graphActions G) μ d S S₀ F hx0 hx1 hg hg1 hh0 hh1
      hsmall hS hF hδ h0 hd0 hR hb0 hbR hb'0 hb' hbF hD hFull hmarg
    exact hh.trans (le_add_of_nonneg_right (by positivity [batchConstant_nonneg Δ]))
  · have hFe : F=∅ := not_nonempty_iff_eq_empty.mp hFn
    have hdis : Disjoint H S := by
      apply disjoint_left.mpr
      intro i hi hs
      have he := hHS (mem_inter.mpr ⟨hi,hs⟩)
      simp [hFe] at he
    have hheavy : ∀ e, e ∉ D.ordinary → b' ≤ d (D.source e) :=
      fun e he => hbH _ (nonordinary_parent_heavy G H e he)
    have hb := expected_step_bound D (balancedActions D Δ) (balancedConflicts D Δ) q
      hh0 hg.le hp1 hq0 hq1 hφ0 hφ1 hq (balancedConflicts_bound D Δ hin)
      (balancedConflicts_self D Δ) d S hx0 hx1 hR0 hd0 (fun i hi => hdR i (hS hi))
      hy hb0 hbR hb'0 hb' hheavy
    have hc := heavy_charge_le G H S hdis x g b d hg.le (fun i _ => hd0 i)
    have hcm := mul_le_mul_of_nonneg_left hc (mul_nonneg hh0 hg.le)
    have ho : (univ : Finset (relevant D S)).offDiag.card ≤ (relevant D S).card^2 := by
      rw [offDiag_card]
      simp only [card_univ,Fintype.card_coe]
      exact (Nat.sub_le _ _).trans_eq (pow_two _).symm
    have hr := uniform_remainder Δ (relevant D S).card
      (univ : Finset (relevant D S)).offDiag.card hD ho hh0 hg.le hg1 hφ0 hR0
    simp only [hFe,sdiff_empty]
    change μ.expect (fun A => potential (x*Real.exp (-h)) g d (nextAlive D x g d S A)
      (nextCap D d b' A)-potential x g d S b) ≤ _
    change μ.expect _ ≤ _ at hb
    nlinarith only [hb,hcm,hr]

end MetricKMedian.FixedBatch
end
end

end OAI
