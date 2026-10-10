import Mathlib

namespace OAI

/-! A smooth three-parameter family has zero volume in dimension at least four. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs

/-- Extend the map constantly in a complementary coordinate and apply the
same-dimensional zero-Jacobian image theorem. -/
theorem smooth_lower_dimensional_image_null {n : ℕ} (hn : 4 ≤ n)
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) : volume (f '' U) = 0 := by
  let : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin 3)) := inferInstance
  let : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin (n - 3))) := inferInstance
  let : ContinuousSMul ℝ
      (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin (n - 3))) :=
    Prod.continuousSMul
  let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin (n - 3)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp; omega)
  let P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (ContinuousLinearMap.fst ℝ _ _).comp L.toContinuousLinearMap
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := f ∘ P
  have hfd (x : EuclideanSpace ℝ (Fin n)) (hx : P x ∈ U) :
      DifferentiableAt ℝ f (P x) :=
    (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hg (x : EuclideanSpace ℝ (Fin n)) (hx : P x ∈ U) :
      DifferentiableAt ℝ g x := (hfd x hx).comp x P.differentiableAt
  let k : Fin (n - 3) := ⟨0, by omega⟩
  let v : EuclideanSpace ℝ (Fin (n - 3)) := PiLp.single 2 k 1
  have hv : v ≠ 0 := by
    intro he
    have he' := congrArg (fun z : EuclideanSpace ℝ (Fin (n - 3)) => z k) he
    exact one_ne_zero (by simpa only [v, PiLp.single_apply, ite_true, PiLp.zero_apply] using he')
  have hP : P (L.symm (0,v)) = 0 := by
    change (L (L.symm (0,v))).1 = 0
    rw [L.apply_symm_apply]
  have hdet (x : EuclideanSpace ℝ (Fin n)) (hx : P x ∈ U) :
      LinearMap.det (fderiv ℝ g x).toLinearMap = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    intro hi
    have hd : fderiv ℝ g x = (fderiv ℝ f (P x)).comp P := by
      change fderiv ℝ (f ∘ P) x = _
      rw [fderiv_comp x (hfd x hx) P.differentiableAt,
        P.fderiv]
    have he : fderiv ℝ g x (L.symm (0,v)) = fderiv ℝ g x 0 := by
      rw [hd]
      simp only [ContinuousLinearMap.comp_apply, hP, map_zero]
    have hz : L.symm (0,v) = 0 := hi he
    have he' := congrArg (fun z => (L z).2) hz
    exact hv (by simpa using he')
  have hnull : volume (g '' (P ⁻¹' U)) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => fderiv ℝ g x)
    · intro x hx
      exact (hg x hx).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      exact hdet x hx
  have he : g '' (P ⁻¹' U) = f '' U := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨P x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      refine ⟨L.symm (x,0),?_,?_⟩
      · simpa [P] using hx
      · change f (P (L.symm (x,0))) = f x
        congr 1
        simp [P]
  rwa [he] at hnull

/-- A smooth three-parameter family has zero volume in any Euclidean target
of dimension at least four. -/
theorem smooth_lower_dimensional_range_null {n : ℕ} (hn : 4 ≤ n)
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ ∞ f) : volume (Set.range f) = 0 := by
  simpa only [Set.image_univ] using
    smooth_lower_dimensional_image_null hn f Set.univ isOpen_univ hf.contDiffOn

/-- The same null-image fact in the plane-coordinate parameter space used
for a tangent vector and one scalar coefficient. -/
theorem smooth_coordinate_parameter_image_null {n : ℕ} (hn : 4 ≤ n)
    (f : ((Fin 2 → ℝ) × ℝ) → EuclideanSpace ℝ (Fin n))
    (U : Set ((Fin 2 → ℝ) × ℝ)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) : volume (f '' U) = 0 := by
  let : ContinuousSMul ℝ ((Fin 2 → ℝ) × ℝ) := Prod.continuousSMul
  let L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] ((Fin 2 → ℝ) × ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hc : ContDiffOn ℝ ∞ (f ∘ L) (L ⁻¹' U) :=
    hf.comp L.contDiff.contDiffOn (fun _ hx => hx)
  have hnull := smooth_lower_dimensional_image_null hn (f ∘ L) (L ⁻¹' U)
    (hU.preimage L.continuous) hc
  have he : (f ∘ L) '' (L ⁻¹' U) = f '' U := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨L x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨L.symm x,by simpa using hx,by simp⟩
  rwa [he] at hnull

/-- Global version in the coordinate parameter space. -/
theorem smooth_coordinate_parameter_range_null {n : ℕ} (hn : 4 ≤ n)
    (f : ((Fin 2 → ℝ) × ℝ) → EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ ∞ f) : volume (Set.range f) = 0 := by
  simpa only [Set.image_univ] using
    smooth_coordinate_parameter_image_null hn f Set.univ isOpen_univ hf.contDiffOn

end ClosedSurfaceR4.PublishedInputs

end

end OAI
