import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeSystem

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
open OrdinaryCorrelations.SignedTrace
variable {S : PrimeSystem} {h ℓ : ℕ}

lemma kappa_pos : 0 < kappa := by norm_num [kappa, eta, epsilon]
lemma A_pos : 0 < A := Real.exp_pos _
lemma betaC_pos : 0 < betaC := inv_pos.mpr (by linarith [A_pos])
lemma betaC_le_one : betaC ≤ 1 := by
  rw [betaC, inv_le_one₀ (by linarith [A_pos])]
  linarith [A_pos]
lemma A_mul_betaC_le_one : A * betaC ≤ 1 := by
  rw [betaC, ← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith [A_pos])).mpr
  linarith
lemma betaC_mul_exp_le_one : betaC * Real.exp kappa ≤ 1 := by
  rw [betaC, mul_comm, ← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith [A_pos])).mpr
  have he : Real.exp kappa ≤ A := Real.exp_le_exp.mpr (by linarith [kappa_pos])
  linarith

lemma cutoff_le_charge {T : ℝ} (cut : S.Cutoffs T) (d : ℕ)
    (x : S.CoreResidues) :
    cut.value d x ≤ Real.exp (-kappa * (S.harmonicCore - T * Real.sqrt S.harmonicCore)) *
      Real.exp (kappa * S.cutoffCount d x) := by
  rw [← Real.exp_add]
  by_cases hs : (S.cutoffCount d x : ℝ) <
      S.harmonicCore - T * Real.sqrt S.harmonicCore
  · rw [cut.support d x hs]
    exact (Real.exp_pos _).le
  · apply (cut.le_one d x).trans
    apply Real.one_le_exp_iff.mpr
    have hk := mul_nonneg kappa_pos.le (sub_nonneg.mpr (le_of_not_gt hs))
    nlinarith

theorem cutoffProduct_le_charges (w : ClosedLine h ℓ) {T : ℝ}
    (cut : S.Cutoffs T) (x : S.CoreResidues) (origins endpoints : Finset (Fin ℓ)) :
    S.cutoffProduct w cut x ≤
      Real.exp (-kappa * (S.harmonicCore - T * Real.sqrt S.harmonicCore) *
        ((origins.card : ℝ) + endpoints.card)) *
      Real.exp (kappa *
        ((∑ i ∈ origins, (S.cutoffCount (w.label i)
          (S.shiftCore x (w.offset i.castSucc)) : ℝ)) +
         ∑ i ∈ endpoints, (S.cutoffCount (w.label i)
          (S.shiftCore x (w.offset i.succ)) : ℝ))) := by
  let c : ℝ := -kappa * (S.harmonicCore - T * Real.sqrt S.harmonicCore)
  have ho : (∏ i : Fin ℓ, cut.value (w.label i) (S.shiftCore x (w.offset i.castSucc))) ≤
      ∏ i ∈ origins, cut.value (w.label i) (S.shiftCore x (w.offset i.castSucc)) :=
    prod_le_prod_of_subset_of_le_one₀ (subset_univ _)
      (fun i _ => cut.nonneg _ _) (fun i _ _ => cut.le_one _ _)
  have he : (∏ i : Fin ℓ, cut.value (w.label i) (S.shiftCore x (w.offset i.succ))) ≤
      ∏ i ∈ endpoints, cut.value (w.label i) (S.shiftCore x (w.offset i.succ)) :=
    prod_le_prod_of_subset_of_le_one₀ (subset_univ _)
      (fun i _ => cut.nonneg _ _) (fun i _ _ => cut.le_one _ _)
  rw [cutoffProduct, prod_mul_distrib]
  calc
    _ ≤ (∏ i ∈ origins, cut.value (w.label i) (S.shiftCore x (w.offset i.castSucc))) *
        ∏ i ∈ endpoints, cut.value (w.label i) (S.shiftCore x (w.offset i.succ)) :=
      mul_le_mul ho he (prod_nonneg (fun i _ => cut.nonneg _ _))
        (prod_nonneg (fun i _ => cut.nonneg _ _))
    _ ≤ (∏ i ∈ origins, Real.exp c * Real.exp (kappa *
          S.cutoffCount (w.label i) (S.shiftCore x (w.offset i.castSucc)))) *
        ∏ i ∈ endpoints, Real.exp c * Real.exp (kappa *
          S.cutoffCount (w.label i) (S.shiftCore x (w.offset i.succ))) := by
      apply mul_le_mul
      · exact prod_le_prod₀ (fun index _ => cut.nonneg _ _) (fun index _ => cutoff_le_charge cut _ _)
      · exact prod_le_prod₀ (fun index _ => cut.nonneg _ _) (fun index _ => cutoff_le_charge cut _ _)
      · exact prod_nonneg (fun i _ => cut.nonneg _ _)
      · exact prod_nonneg (fun i _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by
      simp_rw [← Real.exp_add, ← Real.exp_sum]
      rw [← Real.exp_add]
      congr 1
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      dsimp [c]
      ring

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
