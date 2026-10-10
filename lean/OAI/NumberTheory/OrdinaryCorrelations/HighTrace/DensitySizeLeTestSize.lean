import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EventuallyConstPowLeExp
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LocalIndicator
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SpecificationPrefactor

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter

lemma densitySize_le_testSize (B C₀ : ℝ) (h L ℓ : ℕ) :
    Specification.densitySize B C₀ h L ≤ PrivateFamily.testSize B C₀ h ℓ L := by
  apply Real.log_le_log (by positivity : 0 < (L:ℝ)*h*Real.exp (B*⌈C₀*Real.log B⌉₊)+2)
  gcongr
  omega

noncomputable def sourceDensityDelta (C₀ : ℝ) (h : ℕ) (B : ℝ) : ℝ :=
  max (Specification.densitySize B C₀ h (pathLength B)/(sourceMinPrime B*Real.log 2))
    ((2+B)/sourceMinPrime B)
noncomputable def densityConstant (C₀ : ℝ) (h : ℕ) : ℝ :=
  (C₀+4*(h:ℝ)+3)/Real.log 2+3

lemma sourceDensityDelta_polynomial (h : ℕ) (C₀ B : ℝ) (hC₀ : 0 ≤ C₀) (hB : 1 ≤ B) :
    sourceDensityDelta C₀ h B ≤ densityConstant C₀ h*B^2/sourceMinPrime B := by
  have hP : 0 < sourceMinPrime B := Real.exp_pos _
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hb2 : B ≤ B^2 := by nlinarith
  have hK := (densitySize_le_testSize B C₀ h (pathLength B) (sourceLength B)).trans
    (source_testSize_polynomial h C₀ B hC₀ hB)
  have hC : 0 ≤ C₀+4*(h:ℝ)+3 := by positivity
  unfold sourceDensityDelta
  apply max_le
  · rw [div_mul_eq_div_div_swap]
    apply div_le_div_of_nonneg_right _ hP.le
    apply (div_le_div_of_nonneg_right hK hlog.le).trans
    unfold densityConstant
    rw [mul_div_right_comm]
    nlinarith [sq_nonneg B]
  · apply div_le_div_of_nonneg_right _ hP.le
    have := div_nonneg hC hlog.le
    unfold densityConstant
    nlinarith

lemma source_deleted_density_envelope (h : ℕ) (B τ C₀ : ℝ)
    (D : (sourceSystem B).DivisorFamily B τ C₀) (hB : 1 ≤ B) :
    deletedDensity D h (pathLength B) ≤
      specificationPrefactor (sourceSystem B) (pathLength B) ⌈C₀*Real.log B⌉₊ * sourceDensityDelta C₀ h B := by
  have hP : 0 < sourceMinPrime B := Real.exp_pos _
  have hK := Specification.densitySize_nonneg (B:=B) (C₀:=C₀) (h:=h) (L:=pathLength B)
  have hm := specificationMajorant_le_filling (D:=D) (h:=h) (L:=pathLength B)
    (sourceMinPrime B) (zero_le_one.trans hB) (source_prime_upper B hB)
  have ht := specificationFilling_sum_le (sourceSystem B) (sourceMinPrime B) B
    (Specification.densitySize B C₀ h (pathLength B)) h (pathLength B) ⌈C₀*Real.log B⌉₊
    hP (zero_le_one.trans hB) hK
    (fun p => ⟨(source_prime_lower B hB p).le,source_prime_upper B hB p⟩)
  exact deletedDensity_le_majorant.trans (hm.trans ht)

theorem source_deleted_density (h : ℕ) (τ C₀ κ : ℝ) (hC₀ : 0 ≤ C₀) (hκ : 0 < κ) :
    ∀ᶠ B : ℝ in atTop, ∀ D : (sourceSystem B).DivisorFamily B τ C₀,
      deletedDensity D h (pathLength B) ≤ (sourceMinPrime B)^(-1+κ) := by
  filter_upwards [source_specification_prefactor C₀ hC₀,
    eventually_const_pow_le_exp_rpow (densityConstant C₀ h) (1-epsilon) (κ/2) 2
      (by norm_num [epsilon]) (by positivity),
    eventually_const_mul_rpow_le (1-rho/4) (1-epsilon) (2/κ) (by norm_num [rho,epsilon]),
    eventually_ge_atTop (1:ℝ)] with B hpref hpoly hdom hB
  intro D
  have hP : 0 < sourceMinPrime B := Real.exp_pos _
  have hδ0 : 0 ≤ sourceDensityDelta C₀ h B :=
    (by unfold sourceMinPrime; positivity : 0 ≤ (2+B)/sourceMinPrime B).trans (le_max_right _ _)
  have hdom' := mul_le_mul_of_nonneg_left hdom (show 0 ≤ κ/2 by positivity)
  have he : (κ/2)*((2/κ)*B^(1-rho/4))=B^(1-rho/4) := by
    field_simp
  rw [he] at hdom'
  calc
    _ ≤ specificationPrefactor (sourceSystem B) (pathLength B) ⌈C₀*Real.log B⌉₊ * sourceDensityDelta C₀ h B :=
      source_deleted_density_envelope h B τ C₀ D hB
    _ ≤ Real.exp (B^(1-rho/4))*(densityConstant C₀ h*B^2/sourceMinPrime B) :=
      mul_le_mul hpref (sourceDensityDelta_polynomial h C₀ B hC₀ hB) hδ0 (Real.exp_pos _).le
    _ ≤ Real.exp (B^(1-rho/4))*(Real.exp ((κ/2)*B^(1-epsilon))/sourceMinPrime B) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpoly hP.le) (Real.exp_pos _).le
    _ ≤ Real.exp ((κ/2)*B^(1-epsilon))*(Real.exp ((κ/2)*B^(1-epsilon))/sourceMinPrime B) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hdom') (by positivity)
    _ = _ := by
      rw [sourceMinPrime,←mul_div_assoc,←Real.exp_add,←Real.exp_sub,
        Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      congr 1
      ring

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
