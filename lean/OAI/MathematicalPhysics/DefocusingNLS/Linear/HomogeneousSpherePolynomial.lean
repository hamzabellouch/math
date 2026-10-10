import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPolarL2
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! # Polynomial moments separate continuous functions on the physical sphere

Coordinate polynomials are dense by Stone-Weierstrass. This is the first
step toward detecting a nonzero spherical harmonic coefficient.
-/

open MeasureTheory Set

namespace DefocusingNLS

noncomputable def physicalSphereCoordinate (i : Fin 12) : C(PhysicalUnitSphere, ℝ) :=
  ⟨fun z => (z.1 : EuclideanSpace ℝ (Fin 12)) i, by fun_prop⟩

noncomputable def physicalSpherePolynomial :
    MvPolynomial (Fin 12) ℝ →ₐ[ℝ] C(PhysicalUnitSphere, ℝ) :=
  MvPolynomial.aeval physicalSphereCoordinate

@[simp] theorem physicalSpherePolynomial_X (i : Fin 12) :
    physicalSpherePolynomial (MvPolynomial.X i) = physicalSphereCoordinate i := by
  simp [physicalSpherePolynomial]

theorem physicalSpherePolynomial_apply (p : MvPolynomial (Fin 12) ℝ)
    (z : PhysicalUnitSphere) :
    physicalSpherePolynomial p z = MvPolynomial.eval (fun i => z.1 i) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [physicalSpherePolynomial]
  | add p q hp hq => simp only [map_add, ContinuousMap.add_apply, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, ContinuousMap.mul_apply, physicalSpherePolynomial_X,
      physicalSphereCoordinate, ContinuousMap.coe_mk, hp, MvPolynomial.eval_X]

theorem physicalSpherePolynomial_separates : physicalSpherePolynomial.range.SeparatesPoints := by
  intro x y hxy
  have hcoord : ∃ i : Fin 12, x.1 i ≠ y.1 i := by
    by_contra! h
    apply hxy
    apply Subtype.ext
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨physicalSphereCoordinate i, ⟨physicalSphereCoordinate i, ?_, rfl⟩, hi⟩
  exact ⟨MvPolynomial.X i, physicalSpherePolynomial_X i⟩

theorem physicalSpherePolynomial_dense :
    physicalSpherePolynomial.range.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    physicalSpherePolynomial.range physicalSpherePolynomial_separates

theorem physicalSphere_real_eq_zero_of_polynomial_moments (f : C(PhysicalUnitSphere, ℝ))
    (hf : ∀ p : MvPolynomial (Fin 12) ℝ,
      ∫ z, physicalSpherePolynomial p z * f z ∂physicalSphereMeasure = 0) : f = 0 := by
  let L : C(PhysicalUnitSphere, ℝ) →L[ℝ] Lp ℝ 2 physicalSphereMeasure :=
    ContinuousMap.toLp 2 physicalSphereMeasure ℝ
  have hclosed : IsClosed {g : C(PhysicalUnitSphere, ℝ) | inner ℝ (L f) (L g) = 0} :=
    isClosed_eq (continuous_const.inner L.continuous) continuous_const
  have hrange : (physicalSpherePolynomial.range : Set C(PhysicalUnitSphere, ℝ)) ⊆
      {g | inner ℝ (L f) (L g) = 0} := by
    rintro g ⟨p, rfl⟩
    change inner ℝ (L f) (L (physicalSpherePolynomial p)) = 0
    simpa only [L, ContinuousMap.inner_toLp, RCLike.conj_to_real] using hf p
  have hmem : f ∈ closure (physicalSpherePolynomial.range : Set C(PhysicalUnitSphere, ℝ)) := by
    change f ∈ physicalSpherePolynomial.range.topologicalClosure
    rw [physicalSpherePolynomial_dense]
    trivial
  have hself := closure_minimal hrange hclosed hmem
  have hzero : L f = 0 := (inner_self_eq_zero).mp hself
  let : physicalSphereMeasure.IsOpenPosMeasure := by
    unfold physicalSphereMeasure
    infer_instance
  apply ContinuousMap.toLp_injective (p := 2) physicalSphereMeasure (𝕜 := ℝ)
  simpa only [map_zero] using hzero

theorem physicalSphere_eq_zero_of_polynomial_moments (f : C(PhysicalUnitSphere, ℂ))
    (hf : ∀ p : MvPolynomial (Fin 12) ℝ,
      ∫ z, (physicalSpherePolynomial p z : ℂ) * f z ∂physicalSphereMeasure = 0) : f = 0 := by
  let fr : C(PhysicalUnitSphere, ℝ) := ⟨fun z => (f z).re, Complex.continuous_re.comp f.continuous⟩
  let fi : C(PhysicalUnitSphere, ℝ) := ⟨fun z => (f z).im, Complex.continuous_im.comp f.continuous⟩
  have hint (p : MvPolynomial (Fin 12) ℝ) :
      Integrable (fun z => (physicalSpherePolynomial p z : ℂ) * f z) physicalSphereMeasure :=
    ((Complex.continuous_ofReal.comp (physicalSpherePolynomial p).continuous).mul
      f.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr : fr = 0 := physicalSphere_real_eq_zero_of_polynomial_moments fr (by
    intro p
    have h := (integral_re (hint p)).trans (congrArg Complex.re (hf p))
    change (∫ z, ((physicalSpherePolynomial p z : ℂ) * f z).re ∂physicalSphereMeasure) =
      (0 : ℂ).re at h
    simpa only [fr, ContinuousMap.coe_mk, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] using h)
  have hi : fi = 0 := physicalSphere_real_eq_zero_of_polynomial_moments fi (by
    intro p
    have h := (integral_im (hint p)).trans (congrArg Complex.im (hf p))
    change (∫ z, ((physicalSpherePolynomial p z : ℂ) * f z).im ∂physicalSphereMeasure) =
      (0 : ℂ).im at h
    simpa only [fi, ContinuousMap.coe_mk, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] using h)
  ext z
  apply Complex.ext
  · exact congrArg (fun g : C(PhysicalUnitSphere, ℝ) => g z) hr
  · exact congrArg (fun g : C(PhysicalUnitSphere, ℝ) => g z) hi

theorem physicalSphere_exists_polynomial_moment (f : C(PhysicalUnitSphere, ℂ)) (hf : f ≠ 0) :
    ∃ p : MvPolynomial (Fin 12) ℝ,
      (∫ z, (physicalSpherePolynomial p z : ℂ) * f z ∂physicalSphereMeasure) ≠ 0 := by
  by_contra! h
  exact hf (physicalSphere_eq_zero_of_polynomial_moments f h)

end DefocusingNLS

end OAI
