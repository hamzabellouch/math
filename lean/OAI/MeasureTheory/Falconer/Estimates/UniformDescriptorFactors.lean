import OAI.MeasureTheory.Falconer.Estimates.DescriptorInverseFactors
import OAI.MeasureTheory.Falconer.Estimates.PatchedInverseFactors

namespace OAI

/-! # One separated factor family for all scales and regularized classes

The countable label includes the scale and class before the operator is
constructed. Thus the constants in `HasOrder` are selected for this whole
family, not separately at each scale.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_descriptor_inverse_factors {I : Type*} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (n j : ℕ) (Q : I → DyadicCube (n+3)) (hQ : ∀ a, 0 < (Q a).side)
    (ρ : I → Measure (Space (n+3))) (f : I → ℝ → ℝ) (N : I → ℕ) (σ : I → ℝ)
    (J i t : I → ℕ) (B : I → Finset PlanarFalconer.PolicyDescriptor)
    (hB : ∀ a b, b ∈ B a → PlanarFalconer.descriptorAnchor b ≤ t a)
    (S : I → PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+3))) :
    ∃ T : SmoothSeparation (I × Space (n+3)) (I × Space (n+3)) (Space (n+3)),
      T.HasOrder
        (fun p z => (descriptorAmbientProduct (Q p.1) (ρ p.1) (f p.1) (N p.1)
          (σ p.1) (J p.1) (i p.1) (B p.1) (S p.1) p.2 z : ℂ))
        (fun p z => (descriptorAmbientProduct (Q p.1) (ρ p.1) (f p.1) (N p.1)
          (σ p.1) (J p.1) (i p.1) (B p.1) (S p.1) p.2 z : ℂ)) (2*j) ∧
      (∀ k : T.index, Measurable (Function.uncurry (T.left k)) ∧
        Measurable (Function.uncurry (T.right k))) ∧
      (∀ p q z, localInverseAmplitude n
        (fun w => (descriptorAmbientProduct (Q p.1) (ρ p.1) (f p.1) (N p.1)
          (σ p.1) (J p.1) (i p.1) (B p.1) (S p.1) p.2 w : ℂ)*
          (descriptorAmbientProduct (Q q.1) (ρ q.1) (f q.1) (N q.1)
          (σ q.1) (J q.1) (i q.1) (B q.1) (S q.1) q.2 w : ℂ)) j z = T.value p q z) ∧
      ∀ w : Sphere (n+3), ∀ k : T.index,
        (∀ p, T.left k p w ≠ 0 → ∀ b ∈ B p.1,
          (p.2,w) ∈ descriptorEndpointGood (Q p.1) (ρ p.1) (f p.1) (N p.1)
            (σ p.1) (J p.1) (i p.1+1) b) ∧
        (∀ p, T.right k p w ≠ 0 → ∀ b ∈ B p.1,
          (p.2,w) ∈ descriptorEndpointGood (Q p.1) (ρ p.1) (f p.1) (N p.1)
            (σ p.1) (J p.1) (i p.1+1) b) := by
  let D := fun l : I × Option (List (Fin (n+3) → Bool)) => fun z =>
    (descriptorClassProduct (Q l.1) (ρ l.1) (f l.1) (N l.1) (σ l.1)
      (J l.1) (i l.1) (B l.1) (S l.1) l.2 z : ℂ)
  have hD : ∀ l, ContDiff ℝ ∞ (D l) := fun l =>
    Complex.ofRealCLM.contDiff.comp (descriptorClassProduct_contDiff
      (Q l.1) (ρ l.1) (f l.1) (N l.1) (σ l.1) (J l.1) (i l.1) (B l.1) (S l.1) l.2)
  let a := fun p : I × Space (n+3) => (p.1,cellLabel (Q p.1) (t p.1) p.2)
  have ha : Measurable a :=
    measurable_fst.prodMk (measurable_from_prod_countable_right
      (fun v => cellLabel_measurable (Q v) (t v)))
  obtain ⟨T,horder,hmeas,hvalue,hsupport⟩ :=
    patched_finite_class_inverse_factors n j D D hD hD a a ha ha
  have he (p : I × Space (n+3)) : D (a p) = fun z =>
      (descriptorAmbientProduct (Q p.1) (ρ p.1) (f p.1) (N p.1) (σ p.1)
        (J p.1) (i p.1) (B p.1) (S p.1) p.2 z : ℂ) := by
    funext z
    exact congrArg (fun b : ℝ => (b : ℂ))
      (congrFun (descriptorAmbientProduct_eq_class (Q p.1) (hQ p.1) (ρ p.1) (f p.1)
        (N p.1) (σ p.1) (J p.1) (i p.1) (t p.1) (B p.1) (hB p.1) (S p.1) p.2) z).symm
  refine ⟨T,?_,hmeas,?_,?_⟩
  · simpa only [he] using horder
  · intro p q z
    simpa only [he] using hvalue p q z
  · intro w k
    constructor
    · intro p hp
      apply descriptorAmbientProduct_complex_tsupport_good
        (Q p.1) (ρ p.1) (f p.1) (N p.1) (σ p.1) (J p.1) (i p.1) (B p.1) (S p.1) p.2 w
      simpa only [he] using (hsupport w k).1 p hp
    · intro p hp
      apply descriptorAmbientProduct_complex_tsupport_good
        (Q p.1) (ρ p.1) (f p.1) (N p.1) (σ p.1) (J p.1) (i p.1) (B p.1) (S p.1) p.2 w
      simpa only [he] using (hsupport w k).2 p hp

end Falconer

end OAI
