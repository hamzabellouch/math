import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullLiveTransformTransfer
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateWeightedSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullTransformTransfer
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOneGiant

namespace OAI

/-! # One giant-prior step with a product bound only on actual coefficient support -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance liveTemplateSum_prime {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, Fact (q j).Prime] [∀ i, Fact (p i).Prime] (i : J ⊕ I) :
    Fact (Sum.elim q p i).Prime := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

local instance liveTemplateSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

/-- The support fields in the full Fourier transfer follow from the
original coefficient. Compensation retains its original independent law;
`α` contains the surviving external priors. -/
theorem movingTemplate_prior_transfer_raw_on_live {σ A : Type} [Fintype σ] [Fintype A]
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
    let Q := fun (u : TreeLeafIndex n × Fin 4 → σ) (p : P) =>
      movingOneGiantModuli (p : ℕ) (value ∘ u)
    let _ : ∀ u p i, NeZero (Q u p i) := fun u p i => by
      cases i with
      | inl _ => exact ⟨(hP p p.property).ne_zero⟩
      | inr j => exact ⟨(hvalue (u j)).ne_zero⟩
    let gQ := fun (u : TreeLeafIndex n × Fin 4 → σ) (p : P) =>
      movingOneGiantFactors (p : ℕ) (value ∘ u) greg ggiant favorable
    let W := movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G n r m v α X y
    Real.exp (-smoothGiantLogNormalizer P φ (G (n + 1))) *
      ‖∑ u : TreeLeafIndex n × Fin 4 → σ, ((∏ i, μ n (u i) : ℝ) : ℂ) *
        ∑ p : P, (smoothGiantPrior P φ (G (n + 1)) p : ℂ) *
          ∑ a, W u p a * movingRegularTransform (Sum.elim (Q u p) (L a))
            (movingSumFactors (Q u p) (L a) (gQ u p) (gL a)) outside.prod (v a)‖ ^ 2 ≤
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
  let : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
  let : ∀ a, Fact (value a).Prime := fun a => ⟨hvalue a⟩
  let : ∀ a i, Fact (((value ∘ y a) i)).Prime := fun a i => ⟨hvalue (y a i)⟩
  let greg := normalizedResidueFamily sets
  let U := fun u : TreeLeafIndex n × Fin 4 → σ => ∏ i, value (u i)
  let Q := fun (u : TreeLeafIndex n × Fin 4 → σ) (p : P) =>
    movingOneGiantModuli (p : ℕ) (value ∘ u)
  let L := fun a => movingOneGiantModuli (X a) (value ∘ y a)
  let : ∀ (u : TreeLeafIndex n × Fin 4 → σ) (p : P) i, Fact (Q u p i).Prime := by
    intro u p i
    cases i with
    | inl _ => exact ⟨hP p p.property⟩
    | inr j => exact ⟨hvalue (u j)⟩
  let gQ := fun (u : TreeLeafIndex n × Fin 4 → σ) (p : P) =>
    movingOneGiantFactors (p : ℕ) (value ∘ u) greg ggiant favorable
  let : ∀ a i, Fact (L a i).Prime := fun a i => by
    cases i <;> dsimp only [L, movingOneGiantModuli, Sum.elim, Function.comp_apply] <;> infer_instance
  let : ∀ a i, NeZero (L a i) := fun a i => by infer_instance
  let gL := fun a => movingOneGiantFactors (X a) (value ∘ y a) greg ggiant favorable
  let W := movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G n r m v α X y
  have hprod (a : A) : (∏ i, L a i) = X a * ∏ i, value (y a i) :=
    movingOneGiantModuli_product (X a) (value ∘ y a)
  have hQprod u p : (∏ i, Q u p i) = (p : ℕ) * U u :=
    movingOneGiantModuli_product (p : ℕ) (value ∘ u)
  have hs u p a (h : W u p a ≠ 0) :=
    movingTemplateTransferWeight_support value outside μ childBound pivotBound V F φ G
      n r m v α X y u p a h
  have hgL a i x : gL a i (-x) = conj (gL a i x) :=
    movingOneGiantFactors_neg (X a) (value ∘ y a) greg ggiant favorable
      (hgiant a) (fun j x => by
        dsimp only [greg]
        rw [normalizedResidueFamily_eq]
        exact normalizedResidueTransform_neg _ x) i x
  have ht := smoothGiantPrior_full_transform_transfer_on_live
    (Y := TreeLeafIndex n × Fin 4 → σ) (A := A)
    (J := Unit ⊕ (TreeLeafIndex n × Fin 4)) (H := Unit ⊕ MovingRegularSlot n r m) P I hP hPI hI φ (G (n + 1)) hφ hpos
    (fun u : TreeLeafIndex n × Fin 4 → σ => ∏ i, μ n (u i))
    (fun u => Finset.prod_nonneg (fun i _ => hμ (u i)))
    (by rw [← Fintype.prod_sum]; simp only [hμmass, Finset.prod_const_one]) U
    (fun u => Finset.prod_pos (fun i _ => (hvalue (u i)).pos)) Q gQ hQprod (.inl ())
    (fun u p i => match i with | .inl _ => ∅ | .inr j => sets (value (u j)))
    (fun u p x => by
      change ‖if favorable (p : ℕ) then complexUnitPhase (ggiant p x) else 0‖ ≤ 1
      split_ifs
      · exact complexUnitPhase_norm_le _
      · simp)
    (fun u p i hi => by
      cases i with
      | inl i => cases i; exact (hi rfl).elim
      | inr j => exact normalizedResidueFamily_eq sets (value (u j)))
    (fun u p i hi => by
      cases i with
      | inl i => cases i; exact (hi rfl).elim
      | inr j => exact hsets (u j))
    (fun u p i hi => by
      cases i with
      | inl i => cases i; exact (hi rfl).elim
      | inr j => exact hcard (u j)) (fun _ => L) (fun _ => gL) (fun _ => hgL) (fun _ => outside.prod) (fun _ => v) W
    (fun u p a hw => ⟨(hs u p a hw).1, (hs u p a hw).2.1⟩)
    (fun u p _ a hw => by
      have h := hs u p a hw
      refine ⟨h.2.2.1, ?_, h.2.2.2.2⟩
      have hc := h.2.2.2.1
      change (∏ i, L a i).Coprime (∏ i, movingOneGiantModuli p (value ∘ u) i) at hc
      simpa only [L, U, movingOneGiantModuli_product, Function.comp_apply] using hc)
    N H T (fun _ _ _ a _ => hv a) (fun u hu p hp a ha => (hprod a).trans_le (hH u hu p hp a ha))
    hscale (fun _ _ _ a hw q hq hd =>
      hlarge a (left_ne_zero_of_mul hw) q hq ((hprod a) ▸ hd))
  with_reducible exact ht

end Ostmann

end OAI
