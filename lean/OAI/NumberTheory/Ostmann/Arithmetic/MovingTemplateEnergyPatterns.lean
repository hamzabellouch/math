import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateDiagonalPatterns
import OAI.NumberTheory.Ostmann.Arithmetic.MovingWeightedDiagonalHistories

namespace OAI

/-! # The actual masked energy is bounded by its original signed pattern means -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateDiagonalEnergy_pattern_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ)
    (n r m : ℕ) (active : MovingRegularSlot n r m → Bool)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (μ : ℕ → P → ℝ) (ν : MovingRegularSlot n r m → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ) (hf : f 0 = 0)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ) (hV : Monotone V)
    (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
    (e : ∀ s : Setoid (Bool × MovingSampleIndex n),
      Fin (N s + 1) ≃ MovingRegularSlot n r m ⊕ Quotient s) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    let Sfreq := (transferFrequencyRange (V n)).erase 0
    let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
      frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
    let small := movingTemplateSmall n r m
    let slot := movingTemplateBulk n r m
    let W := fun s => movingTemplateExternalMultiplier P hP n r m active outside greg s φ
      Jleft Jright diagonal
    let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
      ∑ x : Fin (N s + 1) → P,
        movingOriginalPatternWeight (e s) μ ν Subtype.val n (fun i => Quotient.mk'' i)
          (movingOriginalPatternDiagonalObservable (e s) (trees t) small slot (fun i => Quotient.mk'' i)
            P hP p g Dq (movingPatternRegularSlots (e s) n m small slot).get
            (fun i => active (movingPatternTemplateEquiv n r m (e s) i))
            (frequencyRoot n (trees t false))
            (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
              (movingPatternRegularSlots (e s) n m small slot))
            greg f outside childBound pivotBound ψ X lo hi φ G
            Jleft Jright diagonal u v a b center) x
    ‖movingWeightedDiagonalEnergy p Subtype.val outside μ ν childBound pivotBound V f g Dq
      Finset.univ ψ X lo hi φ G n small (bulkSlotLeaves n m slot) W u v a b center‖ ≤
      ∑ t : FrequencyTree (Sfreq × Sfreq) n, ∑ s : Setoid (Bool × MovingSampleIndex n), ‖term t s‖ := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  apply (movingWeightedDiagonalEnergy_history_bound P outside n m p μ ν childBound pivotBound V
    f hf g Dq ψ X lo hi φ G (movingTemplateSmall n r m)
    (bulkSlotLeaves n m (movingTemplateBulk n r m))
    (fun s => movingTemplateExternalMultiplier P hP n r m active outside greg s φ
      Jleft Jright diagonal) u v a b center hV).trans
  apply Finset.sum_le_sum
  intro t _
  rw [movingTemplateWeightedDiagonalMean_patterns P hP n r m _ active p μ ν g Dq greg _
    f outside childBound pivotBound ψ X lo hi φ G Jleft Jright diagonal u v a b center N e]
  exact norm_sum_le _ _

end Ostmann

end OAI
