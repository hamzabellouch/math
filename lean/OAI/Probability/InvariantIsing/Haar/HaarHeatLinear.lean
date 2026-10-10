import OAI.Probability.InvariantIsing.Haar.HaarPolynomialHeat

namespace OAI

/-! Differentiating linear observables of the finite polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial
namespace InvariantIsing

def haarPolynomialLinearCoordinates {N d : ℕ} (F : MatrixPolynomial N →ₗ[ℝ] ℝ) :
    HaarPolynomialCoordinates N d →L[ℝ] ℝ :=
  (F.comp ((haarPolynomialSpace N d).subtype.comp
    (haarPolynomialCoordinates N d).symm.toLinearMap)).toContinuousLinearMap

lemma haarPolynomialLinearCoordinates_apply {N d : ℕ}
    (F : MatrixPolynomial N →ₗ[ℝ] ℝ) (p : haarPolynomialSpace N d) :
    haarPolynomialLinearCoordinates F (haarPolynomialCoordinates N d p) = F (p : MatrixPolynomial N) := by
  change F (((haarPolynomialCoordinates N d).symm (haarPolynomialCoordinates N d p) :
    haarPolynomialSpace N d) : MatrixPolynomial N) = _
  rw [LinearEquiv.symm_apply_apply]

lemma haarPolynomialHeat_linear_hasDerivAt {N d : ℕ}
    (F : MatrixPolynomial N →ₗ[ℝ] ℝ) (p : haarPolynomialSpace N d) (t : ℝ) :
    HasDerivAt (fun s => F ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N))
      (F (haarPolynomialLaplacian N
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N))) t := by
  let L := haarPolynomialCoordinateLaplacian N d
  let v := haarPolynomialCoordinates N d p
  let ev := (haarPolynomialLinearCoordinates F).comp
    (ContinuousLinearMap.apply ℝ (HaarPolynomialCoordinates N d) v)
  have h := ev.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' L t)
  change HasDerivAt (fun s => ev (NormedSpace.exp (s • L)))
    (ev (L*NormedSpace.exp (t • L))) t at h
  have he (s : ℝ) : ev (NormedSpace.exp (s • L)) =
      F ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N) := rfl
  simp_rw [he] at h
  convert h using 1
  change F _ = haarPolynomialLinearCoordinates F (L (NormedSpace.exp (t • L) v))
  rw [← haarPolynomialCoordinates_heat,haarPolynomialCoordinateLaplacian_apply]
  exact (haarPolynomialLinearCoordinates_apply F (haarPolynomialRestrictedLaplacian N d
    (haarPolynomialHeat N d t p))).symm

end InvariantIsing

end

end OAI
