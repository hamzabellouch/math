import OAI.MeasureTheory.Falconer.Fourier.DescriptorJetMeasurable

namespace OAI

/-! # Reached differentiated masks in positive independent energy

Every unreached occurrence remains in the endpoint transform. The cost of
removing reached factors depends on the fixed total jet order, not on the
number of undifferentiated masks or the scale.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

noncomputable def descriptorJetBound (d K : ℕ) : ℝ :=
  (normalizedDescriptorJet_order_bound d K).choose

theorem descriptorJetBound_one_le (d K : ℕ) : 1 ≤ descriptorJetBound d K :=
  (normalizedDescriptorJet_order_bound d K).choose_spec.1

theorem descriptorJetProduct_norm_le {d K : ℕ} {ι : Type*} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (hsep : ∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z →
      descriptorMaskRadius N σ (b j)/2 ≤ dist w z)
    (horder : (∑ j ∈ F, k j) ≤ K)
    (hv : ∀ j ∈ F, ∀ w l, ‖v j w l‖ ≤ 1) (x : Space d) (w : Sphere d) :
    ‖descriptorJetProduct Q ρ m N σ J i F b S k v x w‖ ≤ (descriptorJetBound d K)^K := by
  have hA := descriptorJetBound_one_le d K
  have hbound := (normalizedDescriptorJet_order_bound d K).choose_spec.2
  rw [descriptorJetProduct,norm_prod]
  calc
    _ ≤ ∏ j ∈ F, (descriptorJetBound d K)^(k j) := by
      apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
      intro j hj
      exact hbound Q ρ m N σ J i (b j) (S (b j)) (hsep j hj) (k j)
        ((Finset.single_le_sum (fun l _ => Nat.zero_le (k l)) hj).trans horder)
        (v j w) (hv j hj w) x w
    _ = (descriptorJetBound d K)^(∑ j ∈ F, k j) := Finset.prod_pow_eq_pow_sum F k _
    _ ≤ (descriptorJetBound d K)^K := pow_le_pow_right₀ hA horder

/-- Evaluate the spatial parameter before proving angular measurability. -/
theorem descriptorJetProduct_fixed_measurable {d : ℕ} {ι : Type*}
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset ι)
    (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (hv : ∀ j ∈ F, Measurable (v j)) (x : Space d) :
    Measurable (fun w => descriptorJetProduct Q ρ m N σ J i F b S k v x w) := by
  exact (descriptorJetProduct_measurable Q ρ m N σ J i F b S k v hv).of_uncurry_left

/-- Bounded angular factors can be removed from two finite endpoint laws. -/
theorem independentAngularEnergy_endpoint_remove_factors {d : ℕ}
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (f g : Space d → Sphere d → ℂ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfC : ∀ x w, ‖f x w‖ ≤ C) (hgD : ∀ x w, ‖g x w‖ ≤ D)
    (p q : Sphere d → ℂ) (hp : Measurable p) (hq : Measurable q)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpA : ∀ w, ‖p w‖ ≤ A) (hqB : ∀ w, ‖q w‖ ≤ B)
    (a t : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure t Ψ)] :
    independentAngularEnergy a t Ψ
      (fun z => p z.2 * endpointTransform μ M f z.1 z.2)
      (fun z => q z.2 * endpointTransform ν P g z.1 z.2) ≤
    A^2*B^2*independentAngularEnergy a t Ψ
      (fun z => endpointTransform μ M f z.1 z.2)
      (fun z => endpointTransform ν P g z.1 z.2) := by
  exact independentAngularEnergy_remove_factors a t Ψ _ _
    (measurable_endpointTransform μ M f hf) (measurable_endpointTransform ν P g hg)
    p q hp hq hA hB
    (div_nonneg (mul_nonneg hC measureReal_nonneg) hM.le)
    (div_nonneg (mul_nonneg hD measureReal_nonneg) hP.le)
    hpA hqB (fun z => endpointTransform_norm_le μ hM f hfC z.1 z.2)
    (fun z => endpointTransform_norm_le ν hP g hgD z.1 z.2)

 theorem endpointTransform_descriptorJetProduct_split {d : ℕ} {ι : Type*}
    (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (X : List (Fin d → Bool)) (μ : Measure (Space d)) (M : ℝ)
    (f : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform (μ.restrict (Q.descendant X).carrier) M
      (fun x w => descriptorJetProduct Q ρ m N σ J i F b S k v x w * f x w) r w =
    descriptorJetProduct Q ρ m N σ J i
      (F.filter (fun j => descriptorAnchor (b j) ≤ X.length)) b S k v (Q.descendant X).center w *
    endpointTransform (μ.restrict (Q.descendant X).carrier) M
      (fun x w => descriptorJetProduct Q ρ m N σ J i
        (F.filter (fun j => X.length < descriptorAnchor (b j))) b S k v x w * f x w) r w := by
  classical
  rw [← endpointTransform_angular_factor (μ.restrict (Q.descendant X).carrier) M
    (fun x w => descriptorJetProduct Q ρ m N σ J i
      (F.filter (fun j => X.length < descriptorAnchor (b j))) b S k v x w * f x w)
    (fun w => descriptorJetProduct Q ρ m N σ J i
      (F.filter (fun j => descriptorAnchor (b j) ≤ X.length)) b S k v (Q.descendant X).center w) r w]
  unfold endpointTransform
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (Q.descendant X).measurable] with x hx
  rw [descriptorJetProduct_reached_split Q hQ ρ m N σ J i F b S k v X hx w]
  ring

 theorem independentAngularEnergy_descriptorJets_remove {d K : ℕ} {ι τ : Type*}
    (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (G : Finset τ) (b : ι → PolicyDescriptor) (c : τ → PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) (k : ι → ℕ) (l : τ → ℕ)
    (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (u : (j : τ) → Sphere d → Fin (l j) → Space d)
    (hsepF : ∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z →
      descriptorMaskRadius N σ (b j)/2 ≤ dist w z)
    (hsepG : ∀ j ∈ G, ∀ w ∈ S (c j), ∀ z ∈ S (c j), w ≠ z →
      descriptorMaskRadius N σ (c j)/2 ≤ dist w z)
    (horderF : (∑ j ∈ F, k j) ≤ K) (horderG : (∑ j ∈ G, l j) ≤ K)
    (hv : ∀ j ∈ F, ∀ w t, ‖v j w t‖ ≤ 1) (hu : ∀ j ∈ G, ∀ w t, ‖u j w t‖ ≤ 1)
    (hvm : ∀ j ∈ F, Measurable (v j)) (hum : ∀ j ∈ G, Measurable (u j))
    (X Y : List (Fin d → Bool)) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M₁ M₂ : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (f g : Space d → Sphere d → ℂ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hfC : ∀ x w, ‖f x w‖ ≤ C₁) (hgC : ∀ x w, ‖g x w‖ ≤ C₂)
    (a t : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure t Ψ)] :
    independentAngularEnergy a t Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M₁
        (fun x w => descriptorJetProduct Q ρ m N σ J i F b S k v x w * f x w) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) M₂
        (fun x w => descriptorJetProduct Q ρ m N σ J i G c S l u x w * g x w) z.1 z.2) ≤
    ((descriptorJetBound d K)^K)^2 * ((descriptorJetBound d K)^K)^2 *
    independentAngularEnergy a t Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M₁
        (fun x w => descriptorJetProduct Q ρ m N σ J i
          (F.filter (fun j => X.length < descriptorAnchor (b j))) b S k v x w * f x w) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) M₂
        (fun x w => descriptorJetProduct Q ρ m N σ J i
          (G.filter (fun j => Y.length < descriptorAnchor (c j))) c S l u x w * g x w) z.1 z.2) := by
  classical
  simp_rw [endpointTransform_descriptorJetProduct_split Q hQ ρ m N σ J i F b S k v,
    endpointTransform_descriptorJetProduct_split Q hQ ρ m N σ J i G c S l u]
  let A := (descriptorJetBound d K)^K
  have hA : 0 ≤ A := pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le d K)) K
  have hF (H : Finset ι) (hH : H ⊆ F) (x : Space d) (w : Sphere d) :
      ‖descriptorJetProduct Q ρ m N σ J i H b S k v x w‖ ≤ A :=
    descriptorJetProduct_norm_le Q ρ m N σ J i H b S k v
      (fun j hj => hsepF j (hH hj)) ((Finset.sum_le_sum_of_subset hH).trans horderF)
      (fun j hj => hv j (hH hj)) x w
  have hG (H : Finset τ) (hH : H ⊆ G) (x : Space d) (w : Sphere d) :
      ‖descriptorJetProduct Q ρ m N σ J i H c S l u x w‖ ≤ A :=
    descriptorJetProduct_norm_le Q ρ m N σ J i H c S l u
      (fun j hj => hsepG j (hH hj)) ((Finset.sum_le_sum_of_subset hH).trans horderG)
      (fun j hj => hu j (hH hj)) x w
  let FX := F.filter (fun j => X.length < descriptorAnchor (b j))
  let GY := G.filter (fun j => Y.length < descriptorAnchor (c j))
  let RX := F.filter (fun j => descriptorAnchor (b j) ≤ X.length)
  let RY := G.filter (fun j => descriptorAnchor (c j) ≤ Y.length)
  let f' := fun x w => descriptorJetProduct Q ρ m N σ J i FX b S k v x w * f x w
  let g' := fun x w => descriptorJetProduct Q ρ m N σ J i GY c S l u x w * g x w
  have hf' : Measurable (Function.uncurry f') :=
    (descriptorJetProduct_measurable Q ρ m N σ J i FX b S k v
      (fun j hj => hvm j ((Finset.filter_subset _ _) hj))).mul hf
  have hg' : Measurable (Function.uncurry g') :=
    (descriptorJetProduct_measurable Q ρ m N σ J i GY c S l u
      (fun j hj => hum j ((Finset.filter_subset _ _) hj))).mul hg
  have hf'C (x : Space d) (w : Sphere d) : ‖f' x w‖ ≤ A*C₁ := by
    change ‖descriptorJetProduct Q ρ m N σ J i FX b S k v x w * f x w‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hF FX (Finset.filter_subset _ _) x w) (hfC x w) (norm_nonneg _) hA
  have hg'C (x : Space d) (w : Sphere d) : ‖g' x w‖ ≤ A*C₂ := by
    change ‖descriptorJetProduct Q ρ m N σ J i GY c S l u x w * g x w‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hG GY (Finset.filter_subset _ _) x w) (hgC x w) (norm_nonneg _) hA
  exact independentAngularEnergy_endpoint_remove_factors
    (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier)
    hM₁ hM₂ f' g' hf' hg' (mul_nonneg hA hC₁) (mul_nonneg hA hC₂) hf'C hg'C
    (fun w => descriptorJetProduct Q ρ m N σ J i RX b S k v (Q.descendant X).center w)
    (fun w => descriptorJetProduct Q ρ m N σ J i RY c S l u (Q.descendant Y).center w)
    (descriptorJetProduct_fixed_measurable Q ρ m N σ J i RX b S k v
      (fun j hj => hvm j ((Finset.filter_subset _ _) hj)) _)
    (descriptorJetProduct_fixed_measurable Q ρ m N σ J i RY c S l u
      (fun j hj => hum j ((Finset.filter_subset _ _) hj)) _)
    hA hA (hF RX (Finset.filter_subset _ _) _) (hG RY (Finset.filter_subset _ _) _) a t Ψ

end Falconer

end OAI
