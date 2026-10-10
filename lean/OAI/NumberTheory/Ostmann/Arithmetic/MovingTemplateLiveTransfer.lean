import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateTransferSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullTransformTransfer
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateLiveRaw

namespace OAI

/-! # The full giant-prior step with its actual supported product bound -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance liveFinalSum_prime {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, Fact (q j).Prime] [∀ i, Fact (p i).Prime] (i : J ⊕ I) :
    Fact (Sum.elim q p i).Prime := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

local instance liveFinalSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

/-- The support fields in the full Fourier transfer follow from the
original coefficient. Compensation retains its original independent law;
`α` contains the surviving external priors. -/
theorem movingTemplate_prior_transfer_on_live {σ A : Type} [Fintype σ] [Fintype A]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (P I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPI : P ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass P φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (X : A → ℕ) (hX : ∀ a, (X a).Prime)
    (y : A → MovingRegularSlot n r m → σ) (v : A → ℤ) (α : A → ℂ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ a x, ggiant (X a) (-x) = conj (ggiant (X a) x))
    (N H T : ℕ) (hv : ∀ a, (v a).natAbs ≤ N)
    (hH : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ), p ∈ I → ∀ a,
      movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G
        n r m v α X y u p a ≠ 0 → X a * (∏ i, value (y a i)) ≤ H)
    (hscale : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 → ∀ p, p ∈ I →
      2 * N * H ≤ T * (p * ∏ i, value (u i)))
    (hlarge : ∀ a, α a ≠ 0 → ∀ q, q.Prime →
      q ∣ X a * (∏ i, value (y a i)) → T < q) :
    let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
    let _ : ∀ a i, Fact (((value ∘ y a) i)).Prime := fun a i => ⟨hvalue (y a i)⟩
    let greg := normalizedResidueFamily sets
    let U := fun u : TreeLeafIndex n × Fin 4 → σ => ∏ i, value (u i)
    let L := fun a => movingOneGiantModuli (X a) (value ∘ y a)
    let _ : ∀ a i, NeZero (L a i) := fun a i => by
      cases i with
      | inl _ => exact ⟨(hX a).ne_zero⟩
      | inr j => exact ⟨(hvalue (y a j)).ne_zero⟩
    let gL := fun a => movingOneGiantFactors (X a) (value ∘ y a) greg ggiant favorable
    let W := movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G n r m v α X y
    Real.exp (-smoothGiantLogNormalizer P φ (G (n + 1))) *
      ‖∑ u : TreeLeafIndex n × Fin 4 → σ, ((∏ i, μ n (u i) : ℝ) : ℂ) *
        ∑ p : P, (smoothGiantPrior P φ (G (n + 1)) p : ℂ) *
          ∑ a, W u p a * movingTaggedTransform
            (Sum.elim (fun b : Bool => if b then (p : ℕ) else X a)
              (value ∘ movingRestoreSample n r m u (y a)))
            (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod (v a)‖ ^ 2 ≤
      (∑ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) * (U u : ℝ) *
        ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
          (pivotDiagonal (fun a => ∏ i, L a i) v
            (movingRegularCoefficient L gL outside.prod (U u) v (W u) p)).re) +
      ‖∑ u : TreeLeafIndex n × Fin 4 → σ, (((∏ i, μ n (u i)) * (U u : ℝ) : ℝ) : ℂ) *
        ∑ s ∈ transferFrequencyRange T, ∑ a, ∑ b,
          if validTransferredPivot I
              (v a * (∏ i, L b i) - v b * (∏ i, L a i)) (s * U u) then
            let p := reconstructedPivot
              (v a * (∏ i, L b i) - v b * (∏ i, L a i)) (s * U u)
            (φ (Real.log p - G (n + 1)) : ℂ) * W u p a * conj (W u p b) *
              movingRegularTransform (Sum.elim (L a) (L b))
                (movingSumFactors (L a) (L b) (gL a) (gL b)) outside.prod s
          else 0‖ := by
  let greg := normalizedResidueFamily sets
  let W := movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G n r m v α X y
  have ht := movingTemplate_prior_transfer_raw_on_live value hvalue outside μ childBound pivotBound V F
    φ G n r m P I hP hPI hI hφ hpos hμ hμmass X hX y v α sets hsets hcard ggiant favorable
    hgiant N H T hv hH hscale hlarge
  have hsum := movingOneGiant_restored_average value (fun z => (hvalue z).ne_zero) n r m
    P (fun p => (hP p p.property).ne_zero) X (fun a => (hX a).ne_zero) y v outside.prod
    greg ggiant favorable (fun u => ((∏ i, μ n (u i) : ℝ) : ℂ))
    (fun p => (smoothGiantPrior P φ (G (n + 1)) p : ℂ)) (fun u p a => W u p a)
  exact (congrArg (fun z : ℂ =>
    Real.exp (-smoothGiantLogNormalizer P φ (G (n + 1))) * ‖z‖ ^ 2) hsum).le.trans ht

end Ostmann

end OAI
