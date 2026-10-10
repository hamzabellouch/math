import OAI.NumberTheory.Ostmann.Arithmetic.MovingTransformedIntegerNode

namespace OAI

/-! # Averaging the forced integer node under the surviving regular law -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateSidePrior {σ : Type} (n r m : ℕ)
    (ν : MovingRegularSlot (n + 1) r m → σ → ℝ) (left : Bool)
    (y : MovingRegularSlot n r m → σ) : ℝ :=
  ∏ i, ν (if left then (.inl i.1, i.2) else (.inr i.1, i.2)) (y i)

noncomputable def movingTemplateIntegerFourierTerm {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (I : Finset ℕ)
    (XL XR : ℕ) (s : ℤ) (left right : MovingRegularSlot n r m → σ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (u : TreeLeafIndex n × Fin 4 → σ) (v w : ℤ) : ℂ :=
  let LH := XL * ∏ i, value (left i)
  let RH := XR * ∏ i, value (right i)
  let p := reconstructedPivot (v * RH - w * LH) (s * ∏ i, value (u i))
  if validTransferredPivot I (v * RH - w * LH) (s * ∏ i, value (u i)) then
    (φ (Real.log p - G (n + 1)) : ℂ) *
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m v
        (movingRestoreSample n r m u left) p XL *
      star (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR) *
      movingTaggedTransform
        (Sum.elim (movingOneGiantModuli XL (value ∘ left))
          (movingOneGiantModuli XR (value ∘ right)))
        (Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
          (Sum.elim (fun _ : Unit => true) (fun _ => false)))
        greg ggiant favorable outside.prod s
  else 0

/-- The next regular template is the independent pair of the two surviving
templates. Compensation remains outside both priors and is sampled once. -/
theorem movingTemplateCoefficient_averaged_integer_node {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (hsV : s.natAbs ≤ V (n + 1))
    (ν : MovingRegularSlot (n + 1) r m → σ → ℝ)
    (XL XR : ℕ) (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR)
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ right, movingTemplateSidePrior n r m ν false right ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < XR * ∏ i, value (right i))
    (hRH : ∀ right, movingTemplateSidePrior n r m ν false right ≠ 0 →
      ∀ q, q.Prime → q ∣ XR * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    (∑ y : MovingRegularSlot (n + 1) r m → σ, ((∏ i, ν i (y i) : ℝ) : ℂ) *
      (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s y XL XR *
        movingTaggedTransform
          (Sum.elim (fun b : Bool => if b then XL else XR) (value ∘ y))
          (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s)) =
    ∑ u : TreeLeafIndex n × Fin 4 → σ,
      (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) *
      ∑ left : MovingRegularSlot n r m → σ, (movingTemplateSidePrior n r m ν true left : ℂ) *
        ∑ right : MovingRegularSlot n r m → σ, (movingTemplateSidePrior n r m ν false right : ℂ) *
          ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
            movingTemplateIntegerFourierTerm value outside μ childBound pivotBound V F φ G n r m I
              XL XR s left right greg ggiant favorable u v.val w.val := by
  let A := fun y : MovingRegularSlot (n + 1) r m → σ =>
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s y XL XR *
      movingTaggedTransform
        (Sum.elim (fun b : Bool => if b then XL else XR) (value ∘ y))
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s
  let M := fun u : TreeLeafIndex n × Fin 4 → σ =>
    (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ)
  let B := fun left right u =>
    ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
      movingTemplateIntegerFourierTerm value outside μ childBound pivotBound V F φ G n r m I
        XL XR s left right greg ggiant favorable u v.val w.val
  have hn left right (hr : movingTemplateSidePrior n r m ν false right ≠ 0) :
      A (movingTemplatePairSample n r m left right) = ∑ u, M u * B left right u := by
    exact movingTemplateCoefficient_transformed_integer_node value outside μ childBound pivotBound V hV
      F hF φ G n r m s hsV left right XL XR hXL hXR hVL hVR I hI hφ hchild
      (hgap right hr) (hRH right hr) hcomp (fun i => (hvalue _).ne_zero)
      (fun i => (hvalue _).ne_zero) greg ggiant favorable
  change (∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * A y) = _
  rw [movingTemplatePair_average]
  change (∑ left, (movingTemplateSidePrior n r m ν true left : ℂ) *
    ∑ right, (movingTemplateSidePrior n r m ν false right : ℂ) *
      A (movingTemplatePairSample n r m left right)) = _
  have he : (∑ left, (movingTemplateSidePrior n r m ν true left : ℂ) *
      ∑ right, (movingTemplateSidePrior n r m ν false right : ℂ) *
        A (movingTemplatePairSample n r m left right)) =
      ∑ left, (movingTemplateSidePrior n r m ν true left : ℂ) *
        ∑ right, (movingTemplateSidePrior n r m ν false right : ℂ) *
          ∑ u, M u * B left right u := by
    apply Finset.sum_congr rfl
    intro left _
    congr 1
    apply Finset.sum_congr rfl
    intro right _
    by_cases hr : movingTemplateSidePrior n r m ν false right = 0
    · simp only [hr, Complex.ofReal_zero, zero_mul]
    · rw [hn left right hr]
  rw [he]
  change _ = ∑ u, M u * ∑ left, (movingTemplateSidePrior n r m ν true left : ℂ) *
    ∑ right, (movingTemplateSidePrior n r m ν false right : ℂ) * B left right u
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext left
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

end Ostmann

end OAI
