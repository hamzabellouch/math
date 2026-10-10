import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeTerms
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateSupportedTransfer

namespace OAI

/-! # Transfer of the original amplitude with its supported product window -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- Specialization to the actual surviving giant, regular tuple and frequency.
The compensation draw and the giant harmonic normalization are unchanged. -/
theorem movingTemplatePrimeAmplitude_transfer_on_support {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : Pg ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ q : Pg, ∀ x, ggiant q (-x) = conj (ggiant q x))
    (H : ℕ)
    (hH : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ), p ∈ I →
      ∀ (q : Pg) (y : MovingRegularSlot n r m → σ) (s : transferFrequencyRange (V n)),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
        n (4 + r) m s.val (movingRestoreSample n r m u y) p q ≠ 0 →
        (q : ℕ) * (∏ i, value (y i)) ≤ H)
    (hscale : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 → ∀ p ∈ I,
      2 * V n * H ≤ V (n + 1) * (p * ∏ i, value (u i)))
    (hlarge : ∀ (q : Pg) (y : MovingRegularSlot n r m → σ) ℓ,
      ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let greg := normalizedResidueFamily sets
    Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n (4 + r) m
        Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m Pg I
        ρ ν greg ggiant favorable +
      ‖movingAmplitudeOffDiagonal value outside μ childBound pivotBound V F φ G n r m Pg I
        ρ ν greg ggiant favorable‖ := by
  intro ρ greg
  let A := MovingAmplitudeIndex σ Pg n r m V
  let X := fun a : A => (a.1 : ℕ)
  let y := fun a : A => a.2.1
  let v := fun a : A => a.2.2.val
  let α := fun a : A => (movingAmplitudePrior Pg n r m V ρ ν a : ℂ)
  let : ∀ a : A, Fact (X a).Prime := fun a => ⟨hPg _ a.1.property⟩
  let : ∀ a : A, ∀ i, Fact (value (y a i)).Prime := fun a i => ⟨hvalue (y a i)⟩
  let : ∀ a : A, ∀ i, NeZero ((value ∘ y a) i) :=
    fun a i => ⟨(hvalue (y a i)).ne_zero⟩
  let L := fun a => movingOneGiantModuli (X a) (value ∘ y a)
  let W := movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G
    n r m v α X y
  have ht := movingTemplate_prior_transfer_on_support value hvalue outside μ childBound pivotBound V F
    φ G n r m Pg I hPg hPI hI hφ hpos hμ hμmass X (fun a => hPg _ a.1.property)
    y v α sets hsets hcard ggiant favorable (fun a => hgiant a.1)
    (V n) H (V (n + 1)) (fun a => (mem_transferFrequencyRange _ _).mp a.2.2.property)
    (fun u hu p hp a ha => hH u hu p hp a.1 (y a) a.2.2 (right_ne_zero_of_mul ha)) hscale (fun a => hlarge a.1 (y a))
  dsimp only at ht
  rw [← movingTemplatePrimeAmplitude_index] at ht
  have hC u p : movingRegularCoefficient L
      (fun a => movingOneGiantFactors (X a) (value ∘ y a) greg ggiant favorable)
      outside.prod (∏ i, value (u i)) v (W u) p =
      fun a => W u p a * movingTaggedTransform (L a)
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable
        (p * (∏ i, value (u i)) * outside.prod) (v a) := by
    funext a
    exact congrArg (fun z => W u p a * z)
      (movingOneGiant_transform_tagged (X a) (value ∘ y a) greg ggiant favorable
        (p * (∏ i, value (u i)) * outside.prod) (v a))
  convert ht using 1
  congr 1
  · unfold movingAmplitudeDiagonal
    apply Finset.sum_congr rfl
    intro u _
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    simp only [movingOneGiantModuli_product, Function.comp_apply]
    exact congrArg (fun c : A → ℂ =>
      (pivotDiagonal (fun a => X a * ∏ i, value (y a i)) v c).re) (hC u p).symm
  · congr 1
    unfold movingAmplitudeOffDiagonal
    apply Finset.sum_congr rfl
    intro u _
    congr 1
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [movingOneGiantModuli_product, Function.comp_apply,
      movingOneGiant_pair_transform_tagged]
    dsimp only [movingTemplateIntegerFourierTerm, movingTemplateTransferWeight, A, X, y, v, α, W]
    split_ifs
    · simp only [map_mul, Complex.conj_ofReal]
      simp only [starRingEnd_apply]
      dsimp only [greg]
      ring
    · simp only [mul_zero]

end Ostmann

end OAI
