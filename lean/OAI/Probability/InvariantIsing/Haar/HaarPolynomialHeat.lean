import OAI.Probability.InvariantIsing.Haar.HaarPolynomialInvariantSpace

namespace OAI

/-! A genuine finite-dimensional heat flow on each invariant polynomial space. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

abbrev HaarPolynomialCoordinates (N d : ℕ) :=
  Fin (Module.finrank ℝ (haarPolynomialSpace N d)) → ℝ

def haarPolynomialCoordinates (N d : ℕ) :
    haarPolynomialSpace N d ≃ₗ[ℝ] HaarPolynomialCoordinates N d :=
  (Module.finBasis ℝ (haarPolynomialSpace N d)).equivFun

def haarPolynomialRestrictedLaplacian (N d : ℕ) :
    Module.End ℝ (haarPolynomialSpace N d) :=
  (haarPolynomialLaplacian N).restrict (fun _ hp => haarPolynomialLaplacian_mem hp)

def haarPolynomialCoordinateLaplacian (N d : ℕ) :
    HaarPolynomialCoordinates N d →L[ℝ] HaarPolynomialCoordinates N d :=
  ((haarPolynomialCoordinates N d).toLinearMap.comp
    ((haarPolynomialRestrictedLaplacian N d).comp
      (haarPolynomialCoordinates N d).symm.toLinearMap)).toContinuousLinearMap

def haarPolynomialHeat (N d : ℕ) (t : ℝ) :
    Module.End ℝ (haarPolynomialSpace N d) :=
  (haarPolynomialCoordinates N d).symm.toLinearMap.comp
    ((NormedSpace.exp (t • haarPolynomialCoordinateLaplacian N d)).toLinearMap.comp
      (haarPolynomialCoordinates N d).toLinearMap)

lemma haarPolynomialHeat_zero (N d : ℕ) (p : haarPolynomialSpace N d) :
    haarPolynomialHeat N d 0 p = p := by
  simp [haarPolynomialHeat]

lemma haarPolynomialCoordinates_heat (N d : ℕ) (t : ℝ)
    (p : haarPolynomialSpace N d) :
    haarPolynomialCoordinates N d (haarPolynomialHeat N d t p) =
      NormedSpace.exp (t • haarPolynomialCoordinateLaplacian N d)
        (haarPolynomialCoordinates N d p) := by
  simp only [haarPolynomialHeat,LinearMap.comp_apply,LinearEquiv.coe_coe,
    ContinuousLinearMap.coe_coe,LinearEquiv.apply_symm_apply]

lemma haarPolynomialCoordinateLaplacian_apply (N d : ℕ)
    (p : haarPolynomialSpace N d) :
    haarPolynomialCoordinateLaplacian N d (haarPolynomialCoordinates N d p) =
      haarPolynomialCoordinates N d (haarPolynomialRestrictedLaplacian N d p) := by
  change haarPolynomialCoordinates N d
    (haarPolynomialRestrictedLaplacian N d
      ((haarPolynomialCoordinates N d).symm (haarPolynomialCoordinates N d p))) = _
  rw [LinearEquiv.symm_apply_apply]

def haarPolynomialCoordinateEval {N d : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    HaarPolynomialCoordinates N d →L[ℝ] ℝ :=
  ((matrixPolynomialEval M).toLinearMap.comp
    ((haarPolynomialSpace N d).subtype.comp
      (haarPolynomialCoordinates N d).symm.toLinearMap)).toContinuousLinearMap

@[simp] lemma haarPolynomialCoordinateEval_apply {N d : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (p : haarPolynomialSpace N d) :
    haarPolynomialCoordinateEval M (haarPolynomialCoordinates N d p) =
      matrixPolynomialEval M (p : MatrixPolynomial N) := by
  simp [haarPolynomialCoordinateEval]

/-- The finite matrix exponential satisfies the actual heat equation under evaluation. -/
theorem haarPolynomialHeat_hasDerivAt {N d : ℕ}
    (p : haarPolynomialSpace N d) (M : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    HasDerivAt (fun s => matrixPolynomialEval M
        ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N))
      (matrixPolynomialEval M (haarPolynomialLaplacian N
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N))) t := by
  let L := haarPolynomialCoordinateLaplacian N d
  let v := haarPolynomialCoordinates N d p
  let ev := (haarPolynomialCoordinateEval M).comp
    (ContinuousLinearMap.apply ℝ (HaarPolynomialCoordinates N d) v)
  have h := ev.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' L t)
  have he (s : ℝ) : ev (NormedSpace.exp (s • L)) =
      matrixPolynomialEval M
        ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N) := rfl
  change HasDerivAt (fun s => ev (NormedSpace.exp (s • L)))
    (ev (L*NormedSpace.exp (t • L))) t at h
  simp_rw [he] at h
  convert h using 1
  change matrixPolynomialEval M _ =
    haarPolynomialCoordinateEval M (L (NormedSpace.exp (t • L) v))
  rw [← haarPolynomialCoordinates_heat,haarPolynomialCoordinateLaplacian_apply]
  exact (haarPolynomialCoordinateEval_apply M (haarPolynomialRestrictedLaplacian N d
    (haarPolynomialHeat N d t p))).symm

end InvariantIsing

end

end OAI
