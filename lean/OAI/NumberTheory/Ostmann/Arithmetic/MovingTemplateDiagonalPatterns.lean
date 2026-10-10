import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateExternalMultiplier

namespace OAI

/-! # The signed equality-pattern expansion of the actual masked diagonal -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateWeightedDiagonalMean_patterns
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m : ℕ)
    (t : Bool → FrequencyTree ℤ n) (active : MovingRegularSlot n r m → Bool)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (μ : ℕ → P → ℝ) (ν : MovingRegularSlot n r m → P → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ)
    (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ)
    (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
    (e : ∀ s : Setoid (Bool × MovingSampleIndex n),
      Fin (N s + 1) ≃ MovingRegularSlot n r m ⊕ Quotient s) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    let small := movingTemplateSmall n r m
    let slot := movingTemplateBulk n r m
    let W := movingTemplateExternalMultiplier P hP n r m active outside greg sreg φ
      Jleft Jright diagonal
    movingWeightedDiagonalMean p Subtype.val outside μ ν childBound pivotBound f g Dq Finset.univ
      ψ X lo hi φ G n t small (bulkSlotLeaves n m slot) W u v a b center =
    ∑ s : Setoid (Bool × MovingSampleIndex n), ∑ x : Fin (N s + 1) → P,
      movingOriginalPatternWeight (e s) μ ν Subtype.val n (fun i => Quotient.mk'' i)
        (movingOriginalPatternDiagonalObservable (e s) t small slot (fun i => Quotient.mk'' i)
          P hP p g Dq (movingPatternRegularSlots (e s) n m small slot).get
          (fun i => active (movingPatternTemplateEquiv n r m (e s) i)) sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots (e s) n m small slot))
          greg f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal u v a b center) x := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  rw [movingWeightedDiagonalMean_patterns p Subtype.val outside μ ν]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  unfold movingOriginalPatternWeight
  congr 1
  unfold movingPatternInjectionGuard
  split_ifs
  · apply movingWeightedDiagonalKernel_fin (e s) t (movingTemplateSmall n r m)
      (movingTemplateBulk n r m) (fun i => Quotient.mk'' i) P hP p g Dq
      (movingPatternRegularSlots (e s) n m (movingTemplateSmall n r m) (movingTemplateBulk n r m)).get
      (fun i => active (movingPatternTemplateEquiv n r m (e s) i))
      (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
        (movingPatternRegularSlots (e s) n m (movingTemplateSmall n r m) (movingTemplateBulk n r m)))
      greg sreg f outside childBound pivotBound ψ X lo hi φ G Jleft Jright diagonal u v a b center
    intro z y
    exact movingTemplateExternalMultiplier_pattern P hP n r m (e s) active outside greg sreg φ
      Jleft Jright diagonal x z y
  · rfl

end Ostmann

end OAI
