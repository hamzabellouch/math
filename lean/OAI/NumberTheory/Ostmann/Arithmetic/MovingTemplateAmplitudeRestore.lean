import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateAmplitude

namespace OAI

/-! # Restoring the original independent compensation law in the amplitude -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateRestoredPrior {σ : Type} (n r m : ℕ)
    (μ : σ → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ) :
    MovingRegularSlot n (4 + r) m → σ → ℝ := fun i =>
  Sum.elim (fun _ => μ) ν ((movingReverseTemplate n r m).symm i)

/-- The original current amplitude is the giant-transfer expression with
one shared compensation draw outside its two giant and frequency sums. -/
theorem movingTemplatePrimeAmplitude_restore {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg : Finset ℕ) (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n (4 + r) m
      Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable =
    ∑ u : TreeLeafIndex n × Fin 4 → σ, ((∏ i, μ n (u i) : ℝ) : ℂ) *
      ∑ XL : Pg, (ρ XL : ℂ) * ∑ XR : Pg, (ρ XR : ℂ) *
        ∑ s : transferFrequencyRange (V n),
          ∑ y : MovingRegularSlot n r m → σ, ((∏ i, ν i (y i) : ℝ) : ℂ) *
            (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m
              s.val (movingRestoreSample n r m u y) XL XR *
              movingTaggedTransform
                (Sum.elim (fun b : Bool => if b then (XL : ℕ) else (XR : ℕ))
                  (value ∘ movingRestoreSample n r m u y))
                (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s.val) := by
  unfold movingTemplatePrimeAmplitude
  have hinner (XL XR : Pg) (s : transferFrequencyRange (V n)) :=
    movingReverseTemplate_average n r m (movingTemplateRestoredPrior n r m (μ n) ν)
      (fun y => movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
        n (4 + r) m s.val y XL XR *
        movingTaggedTransform
          (Sum.elim (fun b : Bool => if b then (XL : ℕ) else (XR : ℕ)) (value ∘ y))
          (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s.val)
  simp_rw [hinner]
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext XL
    arg 2
    ext XR
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext XL
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro XL _
  apply Finset.sum_congr rfl
  intro XR _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  simp only [movingTemplateRestoredPrior, Equiv.symm_apply_apply, Sum.elim_inl,
    Sum.elim_inr]
  ring

end Ostmann

end OAI
