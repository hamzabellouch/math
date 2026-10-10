import OAI.NumberTheory.DirichletL.Detector.LowMellin

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowAdditiveCoefficient (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) : ℂ :=
  if ∀P∈C.excluded,¬P∣s.val then
    let a := primaryGenerator s.val
    let ha := supported_primaryGenerator_ne_zero s.val s.property
    let q : ℝ := Ideal.absNorm s.val
    (Y:ℂ)⁻¹*W1 (q/Y)*idealRowHom C.generator s.val/(C.tau*C.residueMonoid a)*
      ((q/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-m)
  else 0

def lowPhysicalScale (C : CalibrationData) (X Y : ℝ) : ℝ := elementNorm C.generator*X*Y

def lowRowMellinIntegrand (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) (v : ℝ) : ℂ :=
  mellin W0 ((v:ℂ)*Complex.I)*Ω (elementNorm r.2/lowPhysicalScale C X Y)*C.residueMonoid r.2*
    ((elementNorm r.2/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
      lowAdditiveCoefficient C W1 Y r.1 r.2 v

lemma calibration_elementNorm_pos (C : CalibrationData) : 0<elementNorm C.generator := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))

lemma lowPhysicalScale_pos (C : CalibrationData) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    0<lowPhysicalScale C X Y := mul_pos (mul_pos (calibration_elementNorm_pos C) hX) hY

lemma lowAdditiveCoefficient_outer_zero (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) (h : W1 ((Ideal.absNorm s.val:ℝ)/Y)=0) :
    lowAdditiveCoefficient C W1 Y s m v=0 := by
  unfold lowAdditiveCoefficient
  split_ifs <;> simp [h]

lemma lowRowMellinIntegrand_nonzero_form (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (hY : 0<Y) (r : PhysicalRowIndex) (v : ℝ)
    (hc : ∀P∈C.excluded,¬P∣r.1.val) :
    lowRowMellinIntegrand C W0 W1 Ω X Y r v=
      ((Y:ℂ)⁻¹*W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*idealRowHom C.generator r.1.val/
        (C.tau*C.residueMonoid (primaryGenerator r.1.val))*
          (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ))*
          (Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
          sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)*
          Ω (elementNorm r.2/lowPhysicalScale C X Y)*C.residueMonoid r.2)*
        (((elementNorm r.2/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
          (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*mellin W0 ((v:ℂ)*Complex.I)) := by
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  have hqc : (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (div_pos hq hY).ne'
  unfold lowRowMellinIntegrand lowAdditiveCoefficient
  rw [ite_eq_left hc]
  dsimp only
  rw [Complex.cpow_add _ _ hqc]
  ring

lemma lowRowMellinIntegrand_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hΩ : Ω 0=0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (r : PhysicalRowIndex) : Integrable (lowRowMellinIntegrand C W0 W1 Ω X Y r) := by
  by_cases hm : r.2=0
  · have he : lowRowMellinIntegrand C W0 W1 Ω X Y r=0 := by
      funext v
      simp [lowRowMellinIntegrand,hm,elementNorm,hΩ]
    rw [he]
    exact integrable_zero _ _ _
  by_cases hc : ∀P∈C.excluded,¬P∣r.1.val
  · have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
    have hmpos : 0<elementNorm r.2 := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
    change Integrable (fun v : ℝ=>lowRowMellinIntegrand C W0 W1 Ω X Y r v)
    simp_rw [lowRowMellinIntegrand_nonzero_form C W0 W1 Ω X Y hY r _ hc]
    exact (low_mellin_ratio_integrable W0 a0 b0 ha0 hW0 hWs _ _
      (div_pos hmpos (lowPhysicalScale_pos C X Y hX hY)) (div_pos hq hY)).const_mul _
  · have he : lowRowMellinIntegrand C W0 W1 Ω X Y r=0 := by
      funext v
      simp [lowRowMellinIntegrand,lowAdditiveCoefficient,hc]
    rw [he]
    exact integrable_zero _ _ _

theorem physicalRowWeight_low_mellin (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowRowMellinIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y r v := by
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  have hΩ : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  by_cases hm : r.2=0
  · have hw : W0 0=0 := by
      by_contra hh
      have hx := (hW0 hh).1
      linarith
    simp [physicalRowWeight,lowRowMellinIntegrand,hm,elementNorm,hw,hΩ,Ω]
  by_cases hc : ∀P∈C.excluded,¬P∣r.1.val
  · have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
    have hmpos : 0<elementNorm r.2 := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
    rw [physicalRowWeight_insert_cutoff C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hY r]
    unfold physicalRowWeight lowRowMellinIntegrand lowAdditiveCoefficient lowPhysicalScale
    dsimp only
    simp only [ite_eq_left hc]
    have hh := physical_radial_low_mellin W0 a0 b0 ha0 hW0 hWs
      (elementNorm C.generator) (Ideal.absNorm r.1.val) X Y (elementNorm r.2)
      (calibration_elementNorm_pos C) hq hX hY hmpos

    calc
      _ = (Ω (elementNorm r.2/(elementNorm C.generator*X*Y))*(Y:ℂ)⁻¹*
        W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*idealRowHom C.generator r.1.val*
        (C.tau*C.residueMonoid (primaryGenerator r.1.val))⁻¹*C.residueMonoid r.2*
        (Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
        sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2))*
        ((Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X):ℂ)⁻¹*
          W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))) := by dsimp only [Ω]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
      _ = _ := by
        rw [hh]
        repeat rw [←integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun v=>by dsimp only [Ω]; ring)
  · simp [physicalRowWeight,lowRowMellinIntegrand,lowAdditiveCoefficient,hc]

lemma lowAdditiveCoefficient_height (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ) (hY : 0<Y)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) :
    lowAdditiveCoefficient C W1 Y s m v=
      (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*lowAdditiveCoefficient C W1 Y s m 0 := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  have hqc : (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (div_pos hq hY).ne'
  unfold lowAdditiveCoefficient
  split_ifs
  · dsimp only
    rw [Complex.cpow_add _ _ hqc]
    simp only [Complex.ofReal_zero,zero_mul,add_zero]
    ring
  · simp

lemma lowAdditiveCoefficient_height_norm (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ) (hY : 0<Y)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) :
    ‖lowAdditiveCoefficient C W1 Y s m v‖=‖lowAdditiveCoefficient C W1 Y s m 0‖ := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  rw [lowAdditiveCoefficient_height C W1 Y hY s m v,norm_mul,
    low_mellin_phase_norm _ v (div_pos hq hY),one_mul]

def lowArithmeticCoefficient (C : CalibrationData) (s : {I : Id // Supported I}) : ℂ :=
  if ∀P∈C.excluded,¬P∣s.val then
    idealRowHom C.generator s.val/(C.tau*C.residueMonoid (primaryGenerator s.val))
  else 0

lemma calibration_residue_inverse_norm (C : CalibrationData) (a : O) : ‖(C.residueMonoid a)⁻¹‖≤1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero)
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  change ‖(C.residue (Ideal.Quotient.mk (Ideal.span {C.generator}) a))⁻¹‖≤1
  simpa only [MulChar.inv_apply_eq_inv'] using
    FiniteRayExpansion.norm_char_le_one C.residue⁻¹ (Ideal.Quotient.mk (Ideal.span {C.generator}) a)

lemma lowArithmeticCoefficient_norm (C : CalibrationData) (s : {I : Id // Supported I}) :
    ‖lowArithmeticCoefficient C s‖≤‖C.tau‖⁻¹ := by
  unfold lowArithmeticCoefficient
  split_ifs
  · simp only [div_eq_mul_inv,mul_inv_rev,norm_mul,norm_inv]
    have hi := calibration_residue_inverse_norm C (primaryGenerator s.val)
    rw [norm_inv] at hi
    have hh := (mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg _)) (idealRowHom_norm C.generator s.val)).trans hi
    simpa only [mul_assoc] using mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg C.tau)) hh
  · simp

lemma lowArithmeticCoefficient_source_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (s : {I : Id // Supported I}) : ‖lowArithmeticCoefficient (calibrationForSet S hS) s‖≤1 := by
  simpa only [calibrationForSet_tau_norm,inv_one] using lowArithmeticCoefficient_norm (calibrationForSet S hS) s

lemma lowAdditiveCoefficient_eq (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) :
    lowAdditiveCoefficient C W1 Y s m v=
      (Y:ℂ)⁻¹*W1 ((Ideal.absNorm s.val:ℝ)/Y)*lowArithmeticCoefficient C s*
        (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*
          (Real.sqrt (Ideal.absNorm s.val):ℂ)⁻¹*
            sexticGauss (primaryGenerator s.val) (supported_primaryGenerator_ne_zero s.val s.property) (-m) := by
  unfold lowAdditiveCoefficient lowArithmeticCoefficient
  split_ifs <;> simp only [mul_zero,zero_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI
