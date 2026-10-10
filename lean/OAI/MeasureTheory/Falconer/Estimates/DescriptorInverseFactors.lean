import OAI.MeasureTheory.Falconer.Estimates.CellClassifier
import OAI.MeasureTheory.Falconer.Estimates.FiniteClassFactors

namespace OAI

/-! # Measurable stationary factors for the actual descriptor product

The finite expansion is applied to the original spatially anchored masks.
Every nonzero factor retains every old descriptor test at its own endpoint.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem descriptor_inverse_factors (n j : ℕ) (Q : DyadicCube (n+3)) (hQ : 0 < Q.side)
    (ρ : Measure (Space (n+3))) (f : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i t : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (hB : ∀ b ∈ B, PlanarFalconer.descriptorAnchor b ≤ t)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+3))) :
    ∃ T : SmoothSeparation (Space (n+3)) (Space (n+3)) (Space (n+3)),
      T.HasOrder (fun x z => (descriptorAmbientProduct Q ρ f N σ J i B S x z : ℂ))
        (fun y z => (descriptorAmbientProduct Q ρ f N σ J i B S y z : ℂ)) (2*j) ∧
      (∀ k : T.index, Measurable (Function.uncurry (T.left k)) ∧
        Measurable (Function.uncurry (T.right k))) ∧
      (∀ x y e, localInverseAmplitude n
        (fun z => (descriptorAmbientProduct Q ρ f N σ J i B S x z : ℂ)*
          (descriptorAmbientProduct Q ρ f N σ J i B S y z : ℂ)) j e = T.value x y e) ∧
      ∀ w : Sphere (n+3),
        ‖(w : Space (n+3))-(gnomonicChart (0 : Space (n+2)) : Space (n+3))‖ ≤ 1/2 →
        ∀ k : T.index,
          (∀ x, T.left k x w ≠ 0 →
            ∀ b ∈ B, (x,w) ∈ descriptorEndpointGood Q ρ f N σ J (i+1) b) ∧
          (∀ y, T.right k y w ≠ 0 →
            ∀ b ∈ B, (y,w) ∈ descriptorEndpointGood Q ρ f N σ J (i+1) b) := by
  let D := fun l z => (descriptorClassProduct Q ρ f N σ J i B S l z : ℂ)
  have hD : ∀ l, ContDiff ℝ ∞ (D l) := fun l =>
    Complex.ofRealCLM.contDiff.comp (descriptorClassProduct_contDiff Q ρ f N σ J i B S l)
  obtain ⟨T,horder,hmeas,hvalue,hsupport⟩ := finite_class_inverse_factors n j D D hD hD
    (cellLabel Q t) (cellLabel Q t) (cellLabel_measurable Q t) (cellLabel_measurable Q t)
  have he (x : Space (n+3)) : D (cellLabel Q t x) =
      fun z => (descriptorAmbientProduct Q ρ f N σ J i B S x z : ℂ) := by
    funext z
    exact congrArg (fun a : ℝ => (a : ℂ))
      (congrFun (descriptorAmbientProduct_eq_class Q hQ ρ f N σ J i t B hB S x) z).symm
  refine ⟨T,?_,hmeas,?_,?_⟩
  · simpa only [he] using horder
  · intro x y e
    simpa only [he] using hvalue x y e
  · intro w hw k
    constructor
    · intro x hx
      apply descriptorAmbientProduct_complex_tsupport_good Q ρ f N σ J i B S x w
      simpa only [he] using (hsupport w hw k).1 x hx
    · intro y hy
      apply descriptorAmbientProduct_complex_tsupport_good Q ρ f N σ J i B S y w
      simpa only [he] using (hsupport w hw k).2 y hy

end Falconer

end OAI
