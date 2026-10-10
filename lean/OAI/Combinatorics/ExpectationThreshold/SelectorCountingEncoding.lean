import OAI.Combinatorics.ExpectationThreshold.SelectorDefinitions

namespace OAI

/-!
# Reconstruction from the actual changed rows

For an earlier coloring, every point outside the changed rows retains its final
color. Inside a changed row its original color is recorded. Thus the changed
subsets and their original labels determine the entire original coloring.
-/

noncomputable section

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

omit [DecidableEq α] in
/-- An original coloring is reconstructed from its changed rows and the
original labels on those rows. No disjointness of ambient row supersets is used. -/
theorem coloring_eq_of_movedRows
    {a b z : Coloring α s} (ha : Earlier a z) (hb : Earlier b z)
    (hrows : ∀ i, movedRow a z i = movedRow b z i)
    (hlabels : ∀ i x, x ∈ movedRow a z i → a x = b x) : a = b := by
  funext x
  by_cases hxa : z x < a x
  · let i : Fin s := ⟨(z x).val,
      Nat.lt_of_lt_of_le hxa (Nat.le_of_lt_succ (a x).isLt)⟩
    apply hlabels i x
    simp only [movedRow, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨rfl, hxa⟩
  · have haeq : a x = z x := le_antisymm (le_of_not_gt hxa) (ha x)
    have hxb : ¬ z x < b x := by
      intro hxb
      let i : Fin s := ⟨(z x).val,
        Nat.lt_of_lt_of_le hxb (Nat.le_of_lt_succ (b x).isLt)⟩
      have hx : x ∈ movedRow b z i := by
        simp only [movedRow, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨rfl, hxb⟩
      rw [← hrows i] at hx
      exact hxa (Finset.mem_filter.mp hx).2.2
    exact haeq.trans (le_antisymm (le_of_not_gt hxb) (hb x)).symm

/-- The unrestricted row record consists of its actual support and its labels. -/
abbrev RawRowEncoding (α : Type*) (s : ℕ) :=
  Σ U : Finset α, (↥U → Color s)

def rawRowEncoding (a z : Coloring α s) (i : Fin s) : RawRowEncoding α s :=
  ⟨movedRow a z i, fun x => a x.1⟩

/-- Reading one point avoids any dependence on the chosen subtype proof. -/
def rawRowLookup (E : RawRowEncoding α s) (x : α) : Option (Color s) :=
  if hx : x ∈ E.1 then some (E.2 ⟨x, hx⟩) else none

/-- The literal row encoding is injective on originals moved only earlier. -/
theorem rawRowEncoding_injective
    {a b z : Coloring α s} (ha : Earlier a z) (hb : Earlier b z)
    (he : ∀ i, rawRowEncoding a z i = rawRowEncoding b z i) : a = b := by
  have hrows : ∀ i, movedRow a z i = movedRow b z i :=
    fun i => congrArg Sigma.fst (he i)
  apply coloring_eq_of_movedRows ha hb hrows
  intro i x hx
  have hx' : x ∈ movedRow b z i := by rw [← hrows i]; exact hx
  have hlookup := congrArg (fun E => rawRowLookup E x) (he i)
  dsimp only [rawRowLookup, rawRowEncoding] at hlookup
  simp only [dite_eq_left hx, dite_eq_left hx'] at hlookup
  exact Option.some.inj hlookup

end TalagrandThreshold.Selector

end

end OAI
