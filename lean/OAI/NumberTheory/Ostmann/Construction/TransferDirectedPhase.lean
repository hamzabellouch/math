import OAI.NumberTheory.Ostmann.Construction.RetainedGroupedPhase

namespace OAI

/-! # The copied local factors form the next actual directed prime phase -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- Characters keep their original slot identity when a slot is copied. -/
def copiedSlotCharacter {H Y : Type*}
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p) :
    (Bool × H) ⊕ Y → ∀ p : ℕ, DirichletCharacter ℂ p
  | .inl (_, h) => χH h
  | .inr y => χY y

noncomputable def copiedSlotUnary {H Y : Type*}
    (q : (Bool × H) ⊕ Y → ℕ) [∀ i, Fact (q i).Prime]
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (v w s : ℤ) : (Bool × H) ⊕ Y → ℂ
  | .inl (true, h) => νL h * χH h (q (.inl (true, h)))
      ((v : ZMod (q (.inl (true, h)))) / (s : ZMod (q (.inl (true, h))))) ^
        b (some (.inl h)) none
  | .inl (false, h) => conj (νR h) * χH h (q (.inl (false, h)))
      ((-w : ZMod (q (.inl (false, h)))) / (s : ZMod (q (.inl (false, h))))) ^
        (-b (some (.inl h)) none)
  | .inr y => νYL y * conj (νYR y)

/-- The previously proved complete transfer identity has exactly the directed
phase maintained by the iteration, with no residual local factors. -/
theorem transfer_directed_phase {H Y : Type*} [Fintype H] [Fintype Y]
    (q : (Bool × H) ⊕ Y → ℕ) [∀ i, Fact (q i).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (M : ℕ) (v w s : ℤ)
    (hrel : v * (∏ h, q (.inl (false, h))) - w * (∏ h, q (.inl (true, h))) = s * M)
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (hM : ∀ i, M.Coprime (q i))
    (hs : ∀ i, IsUnit (s : ZMod (q i)))
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0) :
    retainedPrimePhase (fun h => q (.inl (true, h))) (fun y => q (.inr y)) t χH χY b
        νL νYL M v *
      conj (retainedPrimePhase (fun h => q (.inl (false, h))) (fun y => q (.inr y))
        t χH χY b νR νYR M w) =
      directedPrimePhase q (fun i => copiedSlotCharacter χH χY i (q i))
        (fun i => t (q i)) (copiedSlotUnary q χH b νL νR νYL νYR v w s)
        (transferredGraph b) s := by
  let L : H → ℕ := fun h => q (.inl (true, h))
  let R : H → ℕ := fun h => q (.inl (false, h))
  let U : Y → ℕ := fun y => q (.inr y)
  have heq : transferredLabels L R U = q := by
    funext i
    rcases i with ⟨b, h⟩ | y
    · cases b <;> rfl
    · rfl
  have hco (i) : tupleCofactor (transferredLabels L R U) i = tupleCofactor q i := by rw [heq]
  have ha (i) : transferredAdditiveRow L R U t s i =
      ZMod.stdAddChar (t (q i) * ((tupleCofactor q i : ZMod (q i))⁻¹ * (s : ZMod (q i)))) := by
    rcases i with ⟨b, h⟩ | y
    · cases b <;> simp only [transferredAdditiveRow, hco, L, R, div_eq_mul_inv, mul_comm]
    · simp only [transferredAdditiveRow, hco, U, div_eq_mul_inv, mul_comm]
  have henv {p : ℕ} : transferredLabels (fun h => (L h : ZMod p))
      (fun h => (R h : ZMod p)) (fun y => (U y : ZMod p)) = (fun i => (q i : ZMod p)) := by
    funext i
    rcases i with ⟨b, h⟩ | y
    · cases b <;> rfl
    · rfl
  have hchar (i) : transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s i =
      copiedSlotUnary q χH b νL νR νYL νYR v w s i *
        ∏ j, copiedSlotCharacter χH χY i (q i) (q j : ZMod (q i)) ^ transferredGraph b i j := by
    rcases i with ⟨c, h⟩ | y
    · cases c <;> simp only [transferredCharacterFactor, copiedSlotUnary,
        copiedSlotCharacter, updatedGraphRow, henv, L, R]
    · simp only [transferredCharacterFactor, copiedSlotUnary, copiedSlotCharacter,
        updatedGraphRow, henv, U]
  have hcp : Pairwise (fun i j => (transferredLabels L R U i).Coprime
      (transferredLabels L R U j)) := by simpa only [heq] using hc
  have hMp : ∀ i, M.Coprime (transferredLabels L R U i) := by simpa only [heq] using hM
  have hsp : ∀ i, IsUnit (s : ZMod (transferredLabels L R U i)) := by
    intro i
    rcases i with ⟨c, h⟩ | y
    · cases c <;> exact hs _
    · exact hs _
  have ht := transfer_complete_phase L R U t χH χY b νL νR νYL νYR M v w s
    hrel hcp hMp hsp hb
  refine ht.trans ?_
  unfold directedPrimePhase
  apply Finset.prod_congr rfl
  intro i _
  rw [ha, hchar]
  ring

end Ostmann

end OAI
