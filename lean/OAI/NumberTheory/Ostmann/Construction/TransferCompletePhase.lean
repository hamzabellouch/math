import OAI.NumberTheory.Ostmann.Construction.TransferCharacterProduct

namespace OAI

/-! # The full transfer phase identity on the actual copied tuple -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

section
variable {H Y : Type*} [Fintype H] [Fintype Y]
variable (L : H → ℕ) (U : Y → ℕ)
variable [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]

noncomputable def retainedAdditiveBranch (t : ∀ p : ℕ, ZMod p) (M : ℕ) (v : ℤ) : ℂ :=
  (∏ h, ZMod.stdAddChar (t (L h) * ((v : ZMod (L h)) /
      ((M * (tupleCofactor L h * ∏ y, U y) : ℕ) : ZMod (L h))))) *
  ∏ y, ZMod.stdAddChar (t (U y) * ((v : ZMod (U y)) /
      ((M * (∏ h, L h) * tupleCofactor U y : ℕ) : ZMod (U y))))

noncomputable def retainedCharacterBranch
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νH : H → ℂ) (νY : Y → ℂ) (M : ℕ) : ℂ :=
  (∏ h, νH h * retainedGraphRow (χH h (L h)) b (.inl h) (M : ZMod (L h))
    (Sum.elim (fun k => (L k : ZMod (L h))) (fun y => (U y : ZMod (L h))))) *
  ∏ y, νY y * retainedGraphRow (χY y (U y)) b (.inr y) (M : ZMod (U y))
    (Sum.elim (fun k => (L k : ZMod (U y))) (fun z => (U z : ZMod (U y))))

noncomputable def retainedPrimePhase (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νH : H → ℂ) (νY : Y → ℂ) (M : ℕ) (v : ℤ) : ℂ :=
  retainedAdditiveBranch L U t M v * retainedCharacterBranch L U χH χY b νH νY M

end

/-- This identifies the entire off-diagonal phase, after removal of the
pivot's outgoing row. Its output is the actual directed graph update, with
all additive cofactors and new unary factors included. -/
theorem transfer_complete_phase {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (M : ℕ) (v w s : ℤ)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (hc : Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)))
    (hM : ∀ i, M.Coprime (transferredLabels L R U i))
    (hs : ∀ i, IsUnit (s : ZMod (transferredLabels L R U i)))
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0) :
    retainedPrimePhase L U t χH χY b νL νYL M v *
      conj (retainedPrimePhase R U t χH χY b νR νYR M w) =
    ∏ i, transferredAdditiveRow L R U t s i *
      transferredCharacterFactor L R U χH χY b νL νR νYL νYR v w s i := by
  have hA := transfer_additive_product L R U t M v w s hrel
    (fun h => ⟨hM (.inl (true, h)), transferred_left_denominators L R U hc h⟩)
    (fun h => ⟨hM (.inl (false, h)), transferred_right_denominators L R U hc h⟩)
    (fun y => ⟨hM (.inr y), transferred_outside_denominators L R U hc y⟩)
  change retainedAdditiveBranch L U t M v * conj (retainedAdditiveBranch R U t M w) = _ at hA
  have hC := transfer_character_product L R U χH χY b νL νR νYL νYR M v w s hrel hc hM hs hb
  change retainedCharacterBranch L U χH χY b νL νYL M *
    conj (retainedCharacterBranch R U χH χY b νR νYR M) = _ at hC
  unfold retainedPrimePhase
  rw [map_mul (starRingEnd ℂ)]
  calc
    _ = (retainedAdditiveBranch L U t M v * conj (retainedAdditiveBranch R U t M w)) *
        (retainedCharacterBranch L U χH χY b νL νYL M *
          conj (retainedCharacterBranch R U χH χY b νR νYR M)) := by ring
    _ = _ := by rw [hA, hC, Finset.prod_mul_distrib]

end Ostmann

end OAI
