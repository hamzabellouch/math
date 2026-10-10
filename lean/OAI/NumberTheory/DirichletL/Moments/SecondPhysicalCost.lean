import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondPhysicalCost
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondCanonicalFrequency
open CenteredMomentCanonicalFirst CenteredMomentLogDyadic CenteredMomentSupport
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

theorem actual_normalized_prefactor (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (K:ℝ) (n:Fin 4→ℤ) :
    outerScalar C D K n*normalizer C D U*
      Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/
        (Real.sqrt (C.absNorm:ℝ)*Real.sqrt (D.absNorm:ℝ)*(∏P∈U,P.val).absNorm) := by
  have hcp:0<(C.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hdp:0<(D.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hx:=Real.sqrt_pos.mpr (dyadicScale_pos (n 2))
  have hy:=Real.sqrt_pos.mpr (dyadicScale_pos (n 3))
  rw [normalizer,actual_partitionNormalizer C D hC,outerScalar,
    Real.sqrt_mul (dyadicScale_pos (n 2)).le]
  field_simp

lemma logb_sqrt (Z x:ℝ) (hx:0<x) : Real.logb Z (Real.sqrt x)=Real.logb Z x/2 := by
  rw [Real.sqrt_eq_rpow,Real.logb_rpow_eq_mul_logb_of_pos hx]
  ring

theorem actual_prefactor_log (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (K Z:ℝ) (hK:0<K) (n:Fin 4→ℤ) :
    Real.logb Z (outerScalar C D K n*normalizer C D U*
      Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))=
      Real.logb Z K+
      Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)-
      (Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/2-
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ) := by
  have hc:0<(C.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hg:0<(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by simpa only [Ideal.span_singleton_eq_bot] using commonFrequencyGenerator_ne_zero C D hC))
  have hu:0<((∏P∈U,P.val).absNorm:ℝ) := by
    rw [map_prod,Nat.cast_prod]
    apply Finset.prod_pos
    intro P hP
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by rw [←commonPrime_span C D hC P]; exact (commonPrime_supported C D hC P).1))
  rw [actual_normalized_prefactor C D hC hD,
    Real.logb_div (mul_pos hK hg).ne' (mul_pos (mul_pos (Real.sqrt_pos.mpr hc) (Real.sqrt_pos.mpr hd)) hu).ne',
    Real.logb_mul hK.ne' hg.ne',
    Real.logb_mul (mul_pos (Real.sqrt_pos.mpr hc) (Real.sqrt_pos.mpr hd)).ne' hu.ne',
    Real.logb_mul (Real.sqrt_pos.mpr hc).ne' (Real.sqrt_pos.mpr hd).ne',
    logb_sqrt Z _ hc,logb_sqrt Z _ hd]
  ring

end SevenEighths.CenteredMomentSecondPhysicalCost

end

end OAI
