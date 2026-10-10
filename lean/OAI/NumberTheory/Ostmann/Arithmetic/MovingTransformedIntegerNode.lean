import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateIntegerNode
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOneGiant

namespace OAI

/-! # The integer off-diagonal with the full surviving Fourier factor -/

namespace Ostmann
open scoped Classical BigOperators

/-- The exact node identity retains both giant phases and every regular
Fourier factor. The right side is the off-diagonal in the giant transfer. -/
theorem movingTemplateCoefficient_transformed_integer_node {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (hsV : s.natAbs ≤ V (n + 1))
    (left right : MovingRegularSlot n r m → σ) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR)
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : 2 * pivotBound (n + 1) * childBound (n + 1) < XR * ∏ i, value (right i))
    (hRH : ∀ q, q.Prime → q ∣ XR * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q))
    (hleft : ∀ i, value (left i) ≠ 0) (hright : ∀ i, value (right i) ≠ 0)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s
      (movingTemplatePairSample n r m left right) XL XR *
      movingTaggedTransform
        (Sum.elim (fun b : Bool => if b then XL else XR)
          (value ∘ movingTemplatePairSample n r m left right))
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s =
    ∑ u : TreeLeafIndex n × Fin 4 → σ,
      (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) *
      ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
        let LH := XL * ∏ i, value (left i)
        let RH := XR * ∏ i, value (right i)
        let p := reconstructedPivot (v.val * RH - w.val * LH) (s * ∏ i, value (u i))
        if validTransferredPivot I (v.val * RH - w.val * LH) (s * ∏ i, value (u i)) then
          (φ (Real.log p - G (n + 1)) : ℂ) *
            movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m v.val
              (movingRestoreSample n r m u left) p XL *
            star (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w.val
              (movingRestoreSample n r m u right) p XR) *
            movingTaggedTransform
              (Sum.elim (movingOneGiantModuli XL (value ∘ left))
                (movingOneGiantModuli XR (value ∘ right)))
              (Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
                (Sum.elim (fun _ : Unit => true) (fun _ => false)))
              greg ggiant favorable outside.prod s
        else 0 := by
  have hn := movingTemplateCoefficient_integer_node value outside μ childBound pivotBound V hV
    F hF φ G n r m s hsV left right XL XR hXL hXR hVL hVR I hI hφ hchild hgap hRH hcomp
  have ht := movingTaggedTransform_paired value n r m left right XL XR
    hXL.ne_zero hXR.ne_zero hleft hright greg ggiant favorable outside.prod s
  rw [hn, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [mul_assoc, Finset.sum_mul]
  apply congrArg (fun z : ℂ =>
    (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) * z)
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  dsimp only
  split_ifs
  · congr 1
    exact ht.symm
  · exact zero_mul _

end Ostmann

end OAI
