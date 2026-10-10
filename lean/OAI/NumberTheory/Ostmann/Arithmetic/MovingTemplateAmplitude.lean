import OAI.NumberTheory.Ostmann.Arithmetic.MovingAveragedIntegerNode
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantPrior

namespace OAI

/-! # The original prime amplitude on each restored regular template -/

namespace Ostmann
open scoped Classical BigOperators

/-- The finite prime amplitude, with both giants and every regular slot
sampled from their original laws. The root frequency is not renormalized. -/
noncomputable def movingTemplatePrimeAmplitude {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg : Finset ℕ) (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) : ℂ :=
  ∑ XL : Pg, (ρ XL : ℂ) * ∑ XR : Pg, (ρ XR : ℂ) *
    ∑ s : transferFrequencyRange (V n),
      ∑ y : MovingRegularSlot n r m → σ, ((∏ i, ν i (y i) : ℝ) : ℂ) *
        (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n r m
          s.val y XL XR *
          movingTaggedTransform
            (Sum.elim (fun b : Bool => if b then (XL : ℕ) else (XR : ℕ)) (value ∘ y))
            (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s.val)

/-- The next amplitude is exactly the extended integer off-diagonal,
including its original compensation factors and the two inherited regular
laws. No prime is reweighted or resampled by this identity. -/
theorem movingTemplatePrimeAmplitude_next {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg : Finset ℕ) (hPg : ∀ q ∈ Pg, q.Prime) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot (n + 1) r m → σ → ℝ)
    (hlarge : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right, movingTemplateSidePrior n r m ν false right ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hRH : ∀ XR : Pg, ∀ right, movingTemplateSidePrior n r m ν false right ≠ 0 →
      ∀ q, q.Prime → q ∣ (XR : ℕ) * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G (n + 1) r m
      Pg ρ ν greg ggiant favorable =
    ∑ XL : Pg, (ρ XL : ℂ) * ∑ XR : Pg, (ρ XR : ℂ) *
      ∑ s : transferFrequencyRange (V (n + 1)),
        ∑ u : TreeLeafIndex n × Fin 4 → σ,
          (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) *
            ∑ left : MovingRegularSlot n r m → σ, (movingTemplateSidePrior n r m ν true left : ℂ) *
              ∑ right : MovingRegularSlot n r m → σ, (movingTemplateSidePrior n r m ν false right : ℂ) *
                ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
                  movingTemplateIntegerFourierTerm value outside μ childBound pivotBound V F φ G
                    n r m I XL XR s.val left right greg ggiant favorable u v.val w.val := by
  unfold movingTemplatePrimeAmplitude
  apply Finset.sum_congr rfl
  intro XL _
  congr 1
  apply Finset.sum_congr rfl
  intro XR _
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact movingTemplateCoefficient_averaged_integer_node value hvalue outside μ
    childBound pivotBound V hV F hF φ G n r m s.val
    ((mem_transferFrequencyRange _ _).mp s.property) ν XL XR
    (hPg _ XL.property) (hPg _ XR.property) (hlarge XL) (hlarge XR)
    I hI hφ hchild (hgap XR) (hRH XR) hcomp greg ggiant favorable

end Ostmann

end OAI
