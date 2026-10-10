import Mathlib
import OAI.MathematicalPhysics.BFSS.Cutoffs
import OAI.MathematicalPhysics.BFSS.MixedEnergy

namespace OAI

/-! Deformed smooth charges and quadratic-linear derivative estimates. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

def kineticSkewSymbol (α : SpinIndex) (p : SpaceIndex × ColorIndex N) :
    Fermion N →L[ℝ] Fermion N :=
  ((-Complex.I) • M.kineticComplexSymbol α p).restrictScalars ℝ

def deformedRealField (h m : ℝ) (α : SpinIndex) (x : Boson N) :
    Fermion N →L[ℝ] Fermion N :=
  (M.deformedPotentialMultiplier h m x α).restrictScalars ℝ

lemma deformedRealField_contDiff (h m : ℝ) (α : SpinIndex) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (M.deformedRealField h m α) :=
  (ContinuousLinearMap.restrictScalarsL ℂ (Fermion N) (Fermion N) ℝ ℝ).contDiff.comp
    (M.deformedPotentialMultiplier_contDiff h m α)

lemma kineticSkewSymbol_skew (α : SpinIndex) (p : SpaceIndex × ColorIndex N)
    (z w : Fermion N) :
    inner ℝ (M.kineticSkewSymbol α p z) w = -inner ℝ z (M.kineticSkewSymbol α p w) := by
  have hh : inner ℂ (M.kineticComplexSymbol α p z) w =
      inner ℂ z (M.kineticComplexSymbol α p w) :=
    (M.kineticComplexSymbol_selfAdjoint α p).isSymmetric z w
  have hc : inner ℂ ((-Complex.I) • M.kineticComplexSymbol α p z) w =
      -inner ℂ z ((-Complex.I) • M.kineticComplexSymbol α p w) := by
    rw [inner_smul_left, inner_smul_right, hh]
    simp
  simpa [kineticSkewSymbol, PiLp.inner_apply, real_inner_eq_re_inner, map_sum] using
    congrArg Complex.re hc

lemma deformedRealField_selfAdjoint (h m : ℝ) (α : SpinIndex) (x : Boson N) :
    IsSelfAdjoint (M.deformedRealField h m α x) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro z w
  have hh := (M.cliffordLinear_selfAdjoint (M.deformedPotentialCoefficients h m x α)).isSymmetric z w
  simpa [deformedRealField, deformedPotentialMultiplier, PiLp.inner_apply,
    real_inner_eq_re_inner, map_sum] using congrArg Complex.re hh

lemma deformedRealField_anticommutator (h m : ℝ) (x : Boson N)
    (p : SpaceIndex × ColorIndex N) :
    (∑ α : SpinIndex, (M.kineticSkewSymbol α p * M.deformedRealField h m α x +
      M.deformedRealField h m α x * M.kineticSkewSymbol α p)) = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  have hh := congrArg (fun L : Fermion N →L[ℂ] Fermion N => (-Complex.I) • L z)
    (M.deformed_mixed_anticommutator h m x p)
  simpa only [kineticSkewSymbol, deformedRealField, _root_.sum_apply,
    IsAddApply.add_apply, mul_apply_eq_comp,
    ContinuousLinearMap.coe_restrictScalars', IsSMulApply.smul_apply,
    map_smul, Finset.smul_sum, smul_add, _root_.zero_apply, smul_zero] using hh

def deformedCoreCharge (h m : ℝ) (α : SpinIndex) (f : SmoothCore N) : SmoothCore N :=
  MixedEnergy.firstOrder (M.kineticSkewSymbol α) f +
    MixedEnergy.field (M.deformedRealField h m α) (M.deformedRealField_contDiff h m α) f

lemma kineticSkewCore_eq (α : SpinIndex) (f : SmoothCore N) :
    MixedEnergy.firstOrder (M.kineticSkewSymbol α) f =
      (-Complex.I) • BFSSKinetic.kineticDerivative (M.kineticSymbol α) f := by
  ext x
  rw [MixedEnergy.firstOrder_apply, BFSSKinetic.kineticDerivative_apply]
  simp only [IsSMulApply.smul_apply, Finset.smul_sum, _root_.sum_apply, BFSSKinetic.post_apply,
    kineticSkewSymbol, ContinuousLinearMap.coe_restrictScalars',
    M.kineticComplexSymbol_apply]
  rfl

lemma deformedCoreCharge_apply (h m : ℝ) (α : SpinIndex) (f : SmoothCore N) (x : Boson N) :
    M.deformedCoreCharge h m α f x =
      (-Complex.I) • BFSSKinetic.kineticDerivative (M.kineticSymbol α) f x +
        M.deformedPotentialMultiplier h m x α (f x) := by
  rw [deformedCoreCharge, M.kineticSkewCore_eq]
  rfl

lemma kineticSkewCore_norm (α : SpinIndex) (f : SmoothCore N) :
    ‖coreToL2 (MixedEnergy.firstOrder (M.kineticSkewSymbol α) f)‖^2 =
      (1/2 : ℝ) * ∑ p : SpaceIndex × ColorIndex N,
        ‖coreToL2 (coordinateDerivative p.1 p.2 f)‖^2 := by
  rw [M.kineticSkewCore_eq, map_smul, norm_smul]
  norm_num only [norm_neg, Complex.norm_I, one_mul]
  exact M.literal_kinetic_norm α f

def deformedFermionField (h m : ℝ) (x : Boson N) : Fermion N →L[ℝ] Fermion N :=
  (1/16 : ℝ) • MixedEnergy.remainderField (M.kineticSkewSymbol) (M.deformedRealField h m) x

lemma averaged_core_energy (h m : ℝ) (f : SmoothCore N) :
    (1/16 : ℝ) * ∑ α : SpinIndex, ‖coreToL2 (M.deformedCoreCharge h m α f)‖^2 =
      (1/2 : ℝ) * ∑ p : SpaceIndex × ColorIndex N,
        ‖coreToL2 (coordinateDerivative p.1 p.2 f)‖^2 +
      ∫ x : Boson N, (M.deformedBosonicPotential h m x * ‖f x‖^2 +
        inner ℝ (f x) (M.deformedFermionField h m x (f x))) := by
  have hid := MixedEnergy.averaged_energy_identity (M.kineticSkewSymbol)
    (M.kineticSkewSymbol_skew) (M.deformedRealField h m)
    (M.deformedRealField_contDiff h m) (M.deformedRealField_selfAdjoint h m) f
  change (∑ α : SpinIndex, ‖coreToL2 (M.deformedCoreCharge h m α f)‖^2) = _ at hid
  have hk : (∑ α : SpinIndex, ‖MixedEnergy.toL2
      (MixedEnergy.firstOrder (M.kineticSkewSymbol α) f)‖^2) =
      8 * ∑ p : SpaceIndex × ColorIndex N, ‖coreToL2 (coordinateDerivative p.1 p.2 f)‖^2 := by
    change (∑ α : SpinIndex, ‖coreToL2 (MixedEnergy.firstOrder (M.kineticSkewSymbol α) f)‖^2) = _
    simp only [M.kineticSkewCore_norm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hp : (1/16 : ℝ) * (∑ α : SpinIndex, ‖MixedEnergy.toL2
      (MixedEnergy.field (M.deformedRealField h m α) (M.deformedRealField_contDiff h m α) f)‖^2) =
      ∫ x : Boson N, M.deformedBosonicPotential h m x * ‖f x‖^2 := by
    change (1/16 : ℝ) * (∑ α : SpinIndex, ‖coreToL2
      (MixedEnergy.field (M.deformedRealField h m α) (M.deformedRealField_contDiff h m α) f)‖^2) = _
    simp_rw [coreToL2_norm_sq]
    rw [← integral_finsetSum _ (fun α _ => coreNormSq_integrable _), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    exact M.deformed_potential_average h m x (f x)
  have hf : (1/16 : ℝ) * inner ℝ (MixedEnergy.toL2 f)
      (MixedEnergy.toL2 (MixedEnergy.remainderCore (M.kineticSkewSymbol)
        (M.deformedRealField h m) (M.deformedRealField_contDiff h m) f)) =
      ∫ x : Boson N, inner ℝ (f x) (M.deformedFermionField h m x (f x)) := by
    rw [MixedEnergy.toL2_inner, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [MixedEnergy.remainderCore_apply _ _ _ (M.deformedRealField_anticommutator h m)]
    simp only [deformedFermionField, IsSMulApply.smul_apply, real_inner_smul_right]
  have hip : Integrable (fun x : Boson N => M.deformedBosonicPotential h m x * ‖f x‖^2) volume := by
    have hh : (fun x : Boson N => M.deformedBosonicPotential h m x * ‖f x‖^2) =
        fun x => (1/16 : ℝ) * ∑ α : SpinIndex, ‖MixedEnergy.field (M.deformedRealField h m α)
          (M.deformedRealField_contDiff h m α) f x‖^2 := by
      funext x
      exact (M.deformed_potential_average h m x (f x)).symm
    rw [hh]
    exact (integrable_finsetSum _ (fun α _ => coreNormSq_integrable _)).const_mul _
  have hif : Integrable (fun x : Boson N => inner ℝ (f x) (M.deformedFermionField h m x (f x))) volume := by
    have hh : (fun x : Boson N => inner ℝ (f x) (M.deformedFermionField h m x (f x))) =
        fun x => (1/16 : ℝ) * inner ℝ (f x)
          (MixedEnergy.remainderCore (M.kineticSkewSymbol) (M.deformedRealField h m)
            (M.deformedRealField_contDiff h m) f x) := by
      funext x
      rw [MixedEnergy.remainderCore_apply _ _ _ (M.deformedRealField_anticommutator h m)]
      simp only [deformedFermionField, IsSMulApply.smul_apply, real_inner_smul_right]
    rw [hh]
    exact (MixedEnergy.inner_integrable _ _).const_mul _
  rw [hid, hk, integral_add hip hif, mul_add, mul_add, hp, hf]
  ring

end
end BFSSQuantum.AlgebraData

namespace BilinearGrowth
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma derivative_quadratic_linear (B : E →L[ℝ] E →L[ℝ] F) (L : E →L[ℝ] F)
    (h m : ℝ) (x v : E) :
    fderiv ℝ (fun y => h • B y y + m • L y) x v =
      h • (B x v + B v x) + m • L v := by
  have hb := B.hasFDerivAt_of_bilinear (f := fun y : E => y) (g := fun y : E => y)
    (hasFDerivAt_id x) (hasFDerivAt_id x)
  have hd := (hb.const_smul h).add (L.hasFDerivAt.const_smul m)
  have he := hd.fderiv
  change fderiv ℝ (fun y => h • B y y + m • L y) x = _ at he
  rw [he]
  simp

lemma derivative_quadratic_linear_bound (B : E →L[ℝ] E →L[ℝ] F) (L : E →L[ℝ] F)
    (h m : ℝ) (x v : E) :
    ‖fderiv ℝ (fun y => h • B y y + m • L y) x v‖ ≤
      (2*|h| *‖B‖*‖x‖ + |m| *‖L‖) * ‖v‖ := by
  rw [derivative_quadratic_linear]
  calc
    _ ≤ |h| * (‖B x v‖ + ‖B v x‖) + |m| * ‖L v‖ := by
      grw [norm_add_le, norm_smul, norm_smul, norm_add_le]
      rfl
    _ ≤ |h| * (‖B‖ * ‖x‖ * ‖v‖ + ‖B‖ * ‖v‖ * ‖x‖) +
        |m| * (‖L‖ * ‖v‖) := by
      gcongr
      · exact B.le_opNorm₂ x v
      · exact B.le_opNorm₂ v x
      · exact L.le_opNorm v
    _ = _ := by ring
end
end BilinearGrowth

end OAI
