import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawDecidableEq
import Mathlib.Data.List.Nodup

namespace OAI

/-! # Dyadic proposals from an explicit list without repeated entries -/

namespace ContingencyTables.FairBits
open scoped BigOperators Classical
open ResidualMixture FirstSuccess

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Read a binary index; every index beyond the list gives a hold. -/
def listBitDraw (xs : List X) (k : ℕ) (bits : Fin k → Bool) : Option X :=
  xs[(binaryWordEquiv k bits).val]?

omit [Fintype X] [DecidableEq X] in
lemma listIndex_eq_iff (xs : List X) (hn : xs.Nodup) (k : ℕ)
    (hlen : xs.length ≤ 2^k) (i : ℕ) (hi : i<xs.length)
    (b : Fin (2^k)) : xs[b.val]?=some xs[i] ↔ b=⟨i,hi.trans_le hlen⟩ := by
  constructor
  · intro hb
    obtain ⟨hb,hval⟩ := List.getElem?_eq_some_iff.mp hb
    apply Fin.ext
    exact hn.getElem_inj_iff.mp hval
  · intro hb
    subst b
    exact List.getElem?_eq_getElem hi

lemma listIndex_mass (xs : List X) (hn : xs.Nodup) (k : ℕ)
    (hlen : xs.length ≤ 2^k) (x : X) :
    (mapLaw (uniformLaw (α := Fin (2^k))) (fun b => xs[b.val]?)).mass (some x)=
      if x∈xs then 1/(2:ℚ)^k else 0 := by
  by_cases hx : x∈xs
  · obtain ⟨i,hi,hix⟩ := List.mem_iff_getElem.mp hx
    have he (b : Fin (2^k)) : xs[b.val]?=some x ↔ b=⟨i,hi.trans_le hlen⟩ := by
      rw [←hix]
      exact listIndex_eq_iff xs hn k hlen i hi b
    simp only [mapLaw,uniformLaw,uniformMass,Fintype.card_fin,he,ite_eq_left hx]
    simp
  · have he (b : Fin (2^k)) : xs[b.val]?≠some x := by
      intro hb
      obtain ⟨hb,hval⟩ := List.getElem?_eq_some_iff.mp hb
      exact hx (List.mem_iff_getElem.mpr ⟨b.val,hb,hval⟩)
    simp only [mapLaw,he,ite_false,Finset.sum_const_zero,ite_eq_right hx]

/-- This implementation has exactly the same masses as a uniform
injection into the dyadic code space, with no search for that injection. -/
theorem listBitDraw_mass (xs : List X) (hn : xs.Nodup) (k : ℕ)
    (hlen : xs.length ≤ 2^k) (x : X) :
    (mapLaw (uniformLaw (α := Fin k → Bool)) (listBitDraw xs k)).mass (some x)=
      if x∈xs then 1/(2:ℚ)^k else 0 := by
  have he := map_equiv (binaryWordEquiv k)
    (uniformLaw (α := Fin k → Bool)) (fun b : Fin (2^k) => xs[b.val]?)
  rw [uniform_equiv] at he
  change (mapLaw (uniformLaw (α := Fin k → Bool))
    (fun bits => xs[(binaryWordEquiv k bits).val]?)).mass (some x)=_
  rw [←he]
  exact listIndex_mass xs hn k hlen x

theorem listBitDraw_mass_decidableEq (d : DecidableEq (Option X))
    (xs : List X) (hn : xs.Nodup) (k : ℕ) (hlen : xs.length ≤ 2^k) (x : X) :
    (@mapLaw (Fin k → Bool) (Option X) _ _ d
      (uniformLaw (α := Fin k → Bool)) (listBitDraw xs k)).mass (some x)=
      if x∈xs then 1/(2:ℚ)^k else 0 := by
  have he := mapLaw_mass_decidableEq_irrel d (@Option.instDecidableEq X inferInstance)
    (uniformLaw (α := Fin k → Bool)) (listBitDraw xs k) (some x)
  exact he.trans (listBitDraw_mass xs hn k hlen x)

end ContingencyTables.FairBits

end OAI
