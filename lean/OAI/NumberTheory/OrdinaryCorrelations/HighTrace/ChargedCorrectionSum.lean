import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeVertices

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.FiniteIntegration OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {h ℓ : ℕ}

lemma charged_correction_sum (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hsub : U ⊆ treeVertices w) (hU : ∀ v ∈ U, w.children v = 1) (p : S.Index) :
    (∑ v ∈ treeVertices w,
      (1 - S.beta p ^ w.children v *
        (if S.IsCore p ∧ v ∈ U then Real.exp kappa else 1))) =
      treeDefect w p - (if S.IsCore p then betaC * (Real.exp kappa - 1) * U.card else 0) := by
  by_cases hc : S.IsCore p
  · have hb : S.beta p = betaC := by simp only [beta, amplitude, hc, ite_true, betaC]
    have hp (v : ℤ) :
        (1 - S.beta p ^ w.children v *
          (if S.IsCore p ∧ v ∈ U then Real.exp kappa else 1)) =
        (1 - S.beta p ^ w.children v) -
          (if v ∈ U then betaC * (Real.exp kappa - 1) else 0) := by
      by_cases hv : v ∈ U
      · simp only [hc, hv, and_self, ite_true, hU v hv, pow_one, hb]
        ring
      · simp only [hc, hv, and_false, ite_false, mul_one, sub_zero]
    simp_rw [hp]
    rw [sum_sub_distrib, ite_eq_left hc]
    congr 1
    rw [sum_ite_mem]
    have hu : treeVertices w ∩ U = U := inter_eq_right.mpr hsub
    rw [hu, sum_const, nsmul_eq_mul]
    ring
  · simp only [hc, false_and, ite_false, mul_one, sub_zero, treeDefect]

theorem source_background_mean (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hsub : U ⊆ treeVertices w) (hU : ∀ v ∈ U, w.children v = 1)
    (p : S.Index) (hinj : Set.InjOn (fun v : ℤ => (v : ZMod (p : ℕ))) (treeVertices w)) :
    avg (backgroundMultiplier w U p) = 1 -
      (treeDefect w p - (if S.IsCore p then betaC * (Real.exp kappa - 1) * U.card else 0)) /
        (p : ℝ) := by
  rw [background_mean_exact w U p hinj, charged_correction_sum w U hsub hU p]

lemma background_numerator_nonneg (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hsub : U ⊆ treeVertices w) (hU : ∀ v ∈ U, w.children v = 1) (p : S.Index) :
    0 ≤ treeDefect w p - (if S.IsCore p then betaC * (Real.exp kappa - 1) * U.card else 0) := by
  rw [← charged_correction_sum w U hsub hU p]
  exact sum_nonneg (fun v _ => sub_nonneg.mpr (background_vertex_le_one w U hU p v))

lemma background_mean_le_exp (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hsub : U ⊆ treeVertices w) (hU : ∀ v ∈ U, w.children v = 1)
    (p : S.Index) (hinj : Set.InjOn (fun v : ℤ => (v : ZMod (p : ℕ))) (treeVertices w)) :
    avg (backgroundMultiplier w U p) ≤
      Real.exp (-(treeDefect w p -
        (if S.IsCore p then betaC * (Real.exp kappa - 1) * U.card else 0)) / (p : ℝ)) := by
  rw [source_background_mean w U hsub hU p hinj]
  simpa only [neg_div, sub_eq_add_neg, add_comm] using Real.add_one_le_exp
    (-(treeDefect w p - (if S.IsCore p then betaC * (Real.exp kappa - 1) * U.card else 0)) /
        (p : ℝ))

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
