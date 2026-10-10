import OAI.MeasureTheory.Falconer.Measures.DescriptorProduct

namespace OAI

/-! # Removing exactly the reached descriptor factors from positive energy -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem descriptorProduct_mul_norm_le (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ c ∈ B, ∀ w : Sphere d,
      ∃ z ∈ S c, dist w z ≤ descriptorMaskRadius N σ c/2)
    (b : Space d → Sphere d → ℂ) {C : ℝ}
    (hb : ∀ x w, ‖b x w‖ ≤ C) (x : Space d) (w : Sphere d) :
    ‖(descriptorProduct Q ρ m N σ J i B S x w : ℂ)*b x w‖ ≤ C := by
  have h := descriptorProduct_bounds Q ρ m N σ J i B S hcover x w
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h.1]
  exact (mul_le_mul_of_nonneg_right h.2 (norm_nonneg _)).trans (by simpa using hb x w)

/-- The spatially constant factors are removed only after squaring and
integrating. Every descriptor with an anchor deeper than the child remains. -/
theorem independentAngularEnergy_descriptorProduct_remove
    (Q : DyadicCube d) (hQ : 0 < Q.side) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ c ∈ B, ∀ w : Sphere d,
      ∃ z ∈ S c, dist w z ≤ descriptorMaskRadius N σ c/2)
    (X Y : List (Fin d → Bool)) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M₁ M₂ : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hbC : ∀ x w, ‖b x w‖ ≤ C₁) (hcC : ∀ x w, ‖c x w‖ ≤ C₂)
    (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M₁
        (fun x w => (descriptorProduct Q ρ m N σ J i B S x w : ℂ)*b x w) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) M₂
        (fun x w => (descriptorProduct Q ρ m N σ J i B S x w : ℂ)*c x w) z.1 z.2) ≤
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M₁
        (fun x w => (descriptorProduct Q ρ m N σ J i
          (B.filter (fun t => X.length < descriptorAnchor t)) S x w : ℂ)*b x w) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) M₂
        (fun x w => (descriptorProduct Q ρ m N σ J i
          (B.filter (fun t => Y.length < descriptorAnchor t)) S x w : ℂ)*c x w) z.1 z.2) := by
  let DX := B.filter (fun t => X.length < descriptorAnchor t)
  let DY := B.filter (fun t => Y.length < descriptorAnchor t)
  let RX := B.filter (fun t => descriptorAnchor t ≤ X.length)
  let RY := B.filter (fun t => descriptorAnchor t ≤ Y.length)
  have hsub (F : Finset PolicyDescriptor) (hF : F ⊆ B) :
      ∀ t ∈ F, ∀ w : Sphere d, ∃ z ∈ S t, dist w z ≤ descriptorMaskRadius N σ t/2 :=
    fun t ht => hcover t (hF ht)
  let b' := fun x w => (descriptorProduct Q ρ m N σ J i DX S x w : ℂ)*b x w
  let c' := fun x w => (descriptorProduct Q ρ m N σ J i DY S x w : ℂ)*c x w
  have hb' : Measurable (Function.uncurry b') :=
    ((descriptorProduct_measurable Q ρ m N σ J i DX S).complex_ofReal).mul hb
  have hc' : Measurable (Function.uncurry c') :=
    ((descriptorProduct_measurable Q ρ m N σ J i DY S).complex_ofReal).mul hc
  have hb'C : ∀ x w, ‖b' x w‖ ≤ C₁ :=
    descriptorProduct_mul_norm_le Q ρ m N σ J i DX S (hsub DX (Finset.filter_subset _ _)) b hbC
  have hc'C : ∀ x w, ‖c' x w‖ ≤ C₂ :=
    descriptorProduct_mul_norm_le Q ρ m N σ J i DY S (hsub DY (Finset.filter_subset _ _)) c hcC
  let U := fun z : ℝ × Sphere d =>
    endpointTransform (μ.restrict (Q.descendant X).carrier) M₁ b' z.1 z.2
  let V := fun z : ℝ × Sphere d =>
    endpointTransform (ν.restrict (Q.descendant Y).carrier) M₂ c' z.1 z.2
  let f := fun w : Sphere d =>
    (descriptorProduct Q ρ m N σ J i RX S (Q.descendant X).center w : ℂ)
  let g := fun w : Sphere d =>
    (descriptorProduct Q ρ m N σ J i RY S (Q.descendant Y).center w : ℂ)
  have hf : Measurable f :=
    ((descriptorProduct_measurable Q ρ m N σ J i RX S).comp
      (measurable_const.prodMk measurable_id)).complex_ofReal
  have hg : Measurable g :=
    ((descriptorProduct_measurable Q ρ m N σ J i RY S).comp
      (measurable_const.prodMk measurable_id)).complex_ofReal
  have hf1 (w : Sphere d) : ‖f w‖ ≤ 1 := by
    have h := descriptorProduct_bounds Q ρ m N σ J i RX S
      (hsub RX (Finset.filter_subset _ _)) (Q.descendant X).center w
    simpa only [f,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
  have hg1 (w : Sphere d) : ‖g w‖ ≤ 1 := by
    have h := descriptorProduct_bounds Q ρ m N σ J i RY S
      (hsub RY (Finset.filter_subset _ _)) (Q.descendant Y).center w
    simpa only [g,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
  have hU (z : ℝ × Sphere d) : ‖U z‖ ≤ C₁*(μ.restrict (Q.descendant X).carrier).real univ/M₁ :=
    endpointTransform_norm_le _ hM₁ b' hb'C z.1 z.2
  have hV (z : ℝ × Sphere d) : ‖V z‖ ≤ C₂*(ν.restrict (Q.descendant Y).carrier).real univ/M₂ :=
    endpointTransform_norm_le _ hM₂ c' hc'C z.1 z.2
  have h := independentAngularEnergy_remove_factors a v Ψ U V
    (measurable_endpointTransform _ M₁ b' hb') (measurable_endpointTransform _ M₂ c' hc')
    f g hf hg (by norm_num) (by norm_num) (by positivity) (by positivity) hf1 hg1 hU hV
  simpa only [U,V,f,g,b',c',RX,RY,DX,DY,
    endpointTransform_descriptorProduct_split Q hQ ρ m N σ J i B S,
    one_pow,one_mul] using h

end Falconer

end OAI
