import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplatePatternMultiplier
import OAI.NumberTheory.Ostmann.Arithmetic.MovingWeightedDiagonalRelabel

namespace OAI

/-! # The original exterior multiplier in template and pattern coordinates -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingTemplateExternalMultiplier
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m : ℕ)
    (active : MovingRegularSlot n r m → Bool) (outside : List ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (φ : ℝ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool)
    (x : MovingRegularSlot n r m → P) (z y : ℝ) : ℂ :=
  let q := fun i => (x i : ℕ)
  let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (x i).property⟩
  (giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ) *
    (naturalRegularMultiplier q active s
      (fun i => ((outside.prod * tupleCofactor q i : ℕ) : ZMod (q i)))
      (fun i => greg (q i)) ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℝ)

theorem movingTemplateExternalMultiplier_pattern {C : Type*} {N : ℕ}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m : ℕ)
    (e : Fin (N + 1) ≃ MovingRegularSlot n r m ⊕ C)
    (active : MovingRegularSlot n r m → Bool) (outside : List ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (φ : ℝ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool)
    (x : Fin (N + 1) → P) (z y : ℝ) :
    movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal
      (fun i => x (e.symm (.inl i))) z y =
    movingPatternExternalMultiplier P hP
      (movingPatternRegularSlots e n m (movingTemplateSmall n r m) (movingTemplateBulk n r m)).get
      (fun i => active (movingPatternTemplateEquiv n r m e i))
      (fun x => movingRegularOther (fun j => (x j : ℕ)) outside
        (movingPatternRegularSlots e n m (movingTemplateSmall n r m) (movingTemplateBulk n r m)))
      greg s φ Jleft Jright diagonal x z y := by
  have h := movingTemplate_pattern_multiplier n r m e (fun i => (x i : ℕ))
    (fun i => hP _ (x i).property) active outside greg ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ s
  unfold movingTemplateExternalMultiplier movingPatternExternalMultiplier
  dsimp only
  exact congrArg (fun a : ℝ =>
    (giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ) * a) h.symm

end Ostmann

end OAI
