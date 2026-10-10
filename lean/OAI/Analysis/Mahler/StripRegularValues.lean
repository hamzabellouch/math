import OAI.Analysis.Mahler.InverseRadialRegularity
import OAI.Analysis.Mahler.StripGeometry
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

namespace OAI

/-! Regular positive levels of the literal strip tau. This specializes the
regular-value step to the actual conformal map; it is not a general Sard theorem. -/
noncomputable section
namespace SymmetricMahler
open Set Finset Complex
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

lemma stripTau_eq_sum_normSq_pow (A : J → I → ℝ) (m : ℕ)
    (z : (I → ℝ) × (I → ℝ)) :
    stripTau A m z = ∑ j, Complex.normSq (inverseF (stripCoordinate A z j)) ^ m := by
  simp [stripTau_eq_sum_pow, pow_mul, Complex.normSq_eq_norm_sq]

omit fintypeJ in
lemma stripCoordinate_real_smul [Fintype J] (A : J → I → ℝ) (t : ℝ)
    (z : (I → ℝ) × (I → ℝ)) (j : J) :
    stripCoordinate A (t • z) j = (t : ℂ) * stripCoordinate A z j := by
  have h := congrFun ((stripCoordinateLinear A).map_smul t z) j
  change stripCoordinate A (t • z) j = t • stripCoordinate A z j at h
  simpa only [Complex.real_smul] using h

def stripTauRadialSlope (A : J → I → ℝ) (m : ℕ)
    (z : (I → ℝ) × (I → ℝ)) : ℝ :=
  ∑ j, (m : ℝ) * Complex.normSq (inverseF (stripCoordinate A z j)) ^ (m-1) *
    inverseRadiusRadialSlope (stripCoordinate A z j)

theorem hasDerivAt_stripTau_radial (A : J → I → ℝ) (m : ℕ)
    {z : (I → ℝ) × (I → ℝ)} (hz : z ∈ stripDomain A) :
    HasDerivAt (fun t : ℝ => stripTau A m (t • z)) (stripTauRadialSlope A m z) 1 := by
  simp_rw [stripTau_eq_sum_normSq_pow, stripCoordinate_real_smul]
  unfold stripTauRadialSlope
  convert (HasDerivAt.sum (u := Finset.univ) (fun j _ => by
    simpa using (hasDerivAt_inverseRadius_radial (hz j)).pow m)) using 1 ; try rfl
  ext t
  simp

theorem stripTauRadialSlope_pos (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {z : (I → ℝ) × (I → ℝ)} (hz : z ∈ stripDomain A) (hz0 : z ≠ 0) :
    0 < stripTauRadialSlope A m z := by
  have hn : ∃ j, stripCoordinate A z j ≠ 0 := by
    by_contra h
    push Not at h
    exact hz0 ((stripCoordinate_eq_zero_iff A hA).mp (funext h))
  obtain ⟨j, hj⟩ := hn
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Complex.normSq_nonneg _) _))
      (inverseRadiusRadialSlope_nonneg (hz k))
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    exact mul_pos (mul_pos (by exact_mod_cast hm)
      (pow_pos (Complex.normSq_pos.mpr ((inverseF_eq_zero_iff (hz j)).not.mpr hj)) _))
      (inverseRadiusRadialSlope_pos (hz j) hj)

theorem differentiableAt_stripTau (A : J → I → ℝ) (m : ℕ)
    {z : (I → ℝ) × (I → ℝ)} (hz : z ∈ stripDomain A) :
    DifferentiableAt ℝ (stripTau A m) z := by
  have hcoord : DifferentiableAt ℝ (stripCoordinate A) z :=
    (stripCoordinateLinear A).toContinuousLinearMap.differentiableAt
  have hinv : ∀ j, DifferentiableAt ℝ (fun z => inverseF (stripCoordinate A z j)) z := by
    intro j
    exact ((hasDerivAt_inverseF (hz j)).differentiableAt.restrictScalars ℝ).comp z
      ((ContinuousLinearMap.proj j : (J → ℂ) →L[ℝ] ℂ).differentiableAt.comp z hcoord)
  have heq : stripTau A m = fun z =>
      ∑ j, Complex.normSq (inverseF (stripCoordinate A z j)) ^ m := by
    funext z
    exact stripTau_eq_sum_normSq_pow A m z
  rw [heq]
  have hs : ∀ j, DifferentiableAt ℝ
      (fun z => Complex.normSq (inverseF (stripCoordinate A z j)) ^ m) z := by
    intro j
    have h := hinv j
    simp only [Complex.normSq_apply]
    fun_prop
  convert (DifferentiableAt.sum (u := Finset.univ) (fun j _ => hs j)) using 1 ; try rfl
  ext x
  simp

/-- Every positive value of the actual tau is regular. The derivative is
surjective onto the real scalars, the standard regular-value condition. -/
theorem stripTau_positive_regular (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) {z : (I → ℝ) × (I → ℝ)}
    (hz : z ∈ stripDomain A) (hlevel : stripTau A m z = R) :
    Function.Surjective (fderiv ℝ (stripTau A m) z) := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    rw [stripTau_zero A hm] at hlevel
    linarith
  have hl : HasDerivAt (fun t : ℝ => t • z) z 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).smul_const z)
  have hf : HasFDerivAt (stripTau A m) (fderiv ℝ (stripTau A m) z) ((1 : ℝ) • z) := by
    simpa using (differentiableAt_stripTau A m hz).hasFDerivAt
  have hd := hf.comp_hasDerivAt 1 hl
  have he : (fderiv ℝ (stripTau A m) z) z = stripTauRadialSlope A m z := by
    simpa using hd.unique (hasDerivAt_stripTau_radial A m hz)
  have hp := stripTauRadialSlope_pos A hA hm hz hz0
  intro y
  refine ⟨(y / stripTauRadialSlope A m z) • z, ?_⟩
  rw [map_smul, he]
  change y / stripTauRadialSlope A m z * stripTauRadialSlope A m z = y
  exact div_mul_cancel₀ y hp.ne'

end SymmetricMahler

end

end OAI
