import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedOrigin
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularBasis

namespace OAI

/-! A regular physical basis retaining all derivatives up to the origin. -/

open Set
open scoped ContDiff BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem homogeneousGlued_exists_origin_basis (ell m : ℕ) (νp νm : ℂ)
    (R : ℝ) (hR : 0 < R) (Q : ℝ → ℂ) (hQ : Continuous Q)
    (hQs : ContDiffOn ℝ ∞ Q (Icc 0 R)) :
    ∃ Rp Rm : ℝ → E₄,
      (∀ r ∈ Ioc 0 R, HasDerivAt Rp
        (spectralPhysicalCircularField νp νm ((ell * (ell + 10) : ℕ) : ℂ) m
          (Q r) r (Rp r)) r) ∧
      (∀ r ∈ Ioc 0 R, HasDerivAt Rm
        (spectralPhysicalCircularField νp νm ((ell * (ell + 10) : ℕ) : ℂ) m
          (Q r) r (Rm r)) r) ∧
      LinearIndependent ℂ ![Rp R, Rm R] ∧
      (ContDiff ℝ 2 (fun r => (Rp r).1.1) ∧ ContDiff ℝ 2 (fun r => (Rp r).2.1)) ∧
      (ContDiff ℝ 2 (fun r => (Rm r).1.1) ∧ ContDiff ℝ 2 (fun r => (Rm r).2.1)) ∧
      (ContDiffOn ℝ ∞ (fun r => (Rp r).1.1) (Icc 0 R) ∧
        ContDiffOn ℝ ∞ (fun r => (Rp r).2.1) (Icc 0 R)) ∧
      (ContDiffOn ℝ ∞ (fun r => (Rm r).1.1) (Icc 0 R) ∧
        ContDiffOn ℝ ∞ (fun r => (Rm r).2.1) (Icc 0 R)) := by
  let q := spectralClampedProfile R hR.le Q hQ
  let A := spectralRegularDiagonal m q
  let B := spectralRegularCross m q
  let cp := -Complex.I * νp / 2 + Complex.I * (ell : ℂ) / 2
  let cm := Complex.I * νm / 2 - Complex.I * (ell : ℂ) / 2
  let d := 2 * ell + 11
  let α := spectralRegularSourceBound A B cp cm + 1
  have hbound := spectralRegularSourceBound_nonneg A B cp cm
  have hα : 0 < α := by dsimp only [α]; linarith
  have hgap : spectralRegularSourceBound A B (cp + Complex.I * 0)
      (cm - Complex.I * 0) < 2 * α := by
    simp only [mul_zero, add_zero, sub_zero]
    dsimp only [α]
    linarith
  let v := fun c : ℂ × ℂ => spectralRegularVector d R α hR.le hα A B cp cm c 0
  let s := fun c : ℂ × ℂ => spectralRegularSolutionSource d R α hR.le hα A B cp cm c 0
  let W := fun c : ℂ × ℂ => spectralRegularState d α c (s c)
  have hv (c : ℂ × ℂ) : v c = spectralRegularInitial R α hα.le c +
      spectralRegularPairKernel d R α hR.le hα (s c) :=
    spectralRegularVector_equation d R α hR.le hα A B cp cm c 0 hgap
  have hstate (c : ℂ × ℂ) (r : ℝ) (hr : r ∈ Ioc 0 R) :
      HasDerivAt (W c) (spectralRegularField d (A r) (B r) cp cm r (W c r)) r := by
    simpa only [mul_zero, add_zero, sub_zero] using
      spectralRegularState_hasDerivAt d R α hR.le hα A B (cp + Complex.I * 0)
        (cm - Complex.I * 0) c (v c) (s c) (hv c) rfl r hr
  have hq (r : ℝ) (hr : r ∈ Icc 0 R) : q r = Q r :=
    spectralClampedProfile_eq R hR.le Q hQ r hr
  have hAc : ContDiffOn ℝ ∞ A (Icc 0 R) := by
    have hs := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hQs
    apply (((contDiffOn_const.mul (hQs.pow m)).mul (hs.pow m)) :
      ContDiffOn ℝ ∞ (fun r => ((m + 1 : ℕ) : ℂ) * Q r ^ m * star (Q r) ^ m)
        (Icc 0 R)).congr
    intro r hr
    change spectralRegularDiagonal m q r = _
    rw [spectralRegularDiagonal_apply, hq r hr]
    rfl
  have hBc : ContDiffOn ℝ ∞ B (Icc 0 R) := by
    have hs := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hQs
    apply (((contDiffOn_const.mul (hQs.pow (m + 1))).mul (hs.pow (m - 1))) :
      ContDiffOn ℝ ∞ (fun r => (m : ℂ) * Q r ^ (m + 1) * star (Q r) ^ (m - 1))
        (Icc 0 R)).congr
    intro r hr
    change spectralRegularCross m q r = _
    rw [spectralRegularCross_apply, hq r hr]
    rfl
  have hphys (c : ℂ × ℂ) (r : ℝ) (hr : r ∈ Ioc 0 R) :
      HasDerivAt (spectralAngularPair ell (W c))
        (spectralPhysicalCircularField νp νm ((ell * (ell + 10) : ℕ) : ℂ) m
          (Q r) r (spectralAngularPair ell (W c) r)) r := by
    apply spectralRegularPhysical_hasDerivAt ell m νp νm (Q r) (W c) r hr.1
    have hh := hstate c r hr
    have heA : A r = spectralDiagonalCoefficient m (Q r) := by
      dsimp only [A]
      rw [spectralRegularDiagonal_apply, hq r ⟨hr.1.le, hr.2⟩]
    have heB : B r = spectralCrossCoefficient m (Q r) := by
      dsimp only [B]
      rw [spectralRegularCross_apply, hq r ⟨hr.1.le, hr.2⟩]
    rw [heA, heB] at hh
    exact hh
  have hRank : LinearIndependent ℂ ![W (1, 0) R, W (0, 1) R] :=
    spectralRegular_at_linearIndependent d A B cp cm _ _ R hR
      (spectralRegularState_continuous d α (1, 0) (s (1, 0)))
      (spectralRegularState_continuous d α (0, 1) (s (0, 1)))
      (hstate (1, 0)) (hstate (0, 1))
      (spectralRegularState_initial d α (1, 0) (s (1, 0)))
      (spectralRegularState_initial d α (0, 1) (s (0, 1)))
  have hOrigin (c : ℂ × ℂ) := homogeneousGlued_regular_physical_origin ell d R α hR hα
    A B (cp + Complex.I * 0) (cm - Complex.I * 0) c (v c) (s c) (hv c) rfl hAc hBc
  refine ⟨spectralAngularPair ell (W (1, 0)), spectralAngularPair ell (W (0, 1)),
    hphys (1, 0), hphys (0, 1), spectralAngularPair_rank ell _ _ R hR.ne' hRank,
    homogeneousRegularPhysical_contDiff_two ell d α (1, 0) (s (1, 0)),
    homogeneousRegularPhysical_contDiff_two ell d α (0, 1) (s (0, 1)),
    hOrigin (1, 0), hOrigin (0, 1)⟩

end DefocusingNLS

end OAI
