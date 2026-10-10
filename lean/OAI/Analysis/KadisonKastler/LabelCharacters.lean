import OAI.Analysis.KadisonKastler.FinitePhases
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Sym.Card

namespace OAI

/-!
# Root-of-unity phases indexed by label multisets

The phase space is a finite product of cyclic groups. A multiset gives
its character by pairing the phase coordinates with its multiplicities.
If the word length is less than the root order, no multiplicity can wrap
around, so distinct multisets give orthogonal characters.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q]

def labelDot (s : Multiset ι) : (ι → ZMod q) →+ ZMod q where
  toFun θ := ∑ i, (s.count i : ZMod q) * θ i
  map_zero' := by simp
  map_add' θ η := by simp [mul_add, sum_add_distrib]

def multisetCharacter (s : Multiset ι) : AddChar (ι → ZMod q) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom (labelDot s)

omit [NeZero q] in
@[simp]
theorem labelDot_single (s : Multiset ι) (a : ι) :
    labelDot (q := q) s (Pi.single a 1) = (s.count a : ZMod q) := by
  simp [labelDot, Pi.single_apply, mul_ite]

@[simp]
theorem multisetCharacter_single (s : Multiset ι) (a : ι) :
    multisetCharacter (q := q) s (Pi.single a 1) = ZMod.stdAddChar (s.count a : ZMod q) := by
  simp [multisetCharacter]

omit [NeZero q] in
@[simp]
theorem labelDot_zero (θ : ι → ZMod q) : labelDot (0 : Multiset ι) θ = 0 := by
  simp [labelDot]

omit [NeZero q] in
theorem labelDot_cons (a : ι) (s : Multiset ι) (θ : ι → ZMod q) :
    labelDot (a ::ₘ s) θ = θ a + labelDot s θ := by
  simp only [labelDot, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Multiset.count_cons,
    Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_mul, sum_add_distrib]
  simp [ite_mul, add_comm]

theorem multisetCharacter_cons (a : ι) (s : Multiset ι) (θ : ι → ZMod q) :
    multisetCharacter (a ::ₘ s) θ = ZMod.stdAddChar (θ a) * multisetCharacter s θ := by
  simp [multisetCharacter, labelDot_cons, AddChar.map_add_eq_mul]

/-- This is exactly the phase monomial, including label multiplicities. -/
theorem multisetCharacter_eq_prod (s : Multiset ι) (θ : ι → ZMod q) :
    multisetCharacter s θ = (s.map (fun a => ZMod.stdAddChar (θ a))).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [multisetCharacter]
  | @cons a s ih => simp [multisetCharacter_cons, ih]

/-- A root order larger than the word length separates all label multisets. -/
theorem multisetCharacter_injective {r : ℕ} (hr : r < q) :
    Function.Injective (fun s : Sym ι r => multisetCharacter (q := q) (s : Multiset ι)) := by
  intro s t hst
  apply Sym.ext
  apply Multiset.ext'
  intro a
  have he := congrArg (fun χ : AddChar (ι → ZMod q) ℂ => χ (Pi.single a 1)) hst
  simp only [multisetCharacter_single] at he
  have hz := ZMod.injective_stdAddChar he
  have hs : (s : Multiset ι).count a < q :=
    lt_of_le_of_lt (by simpa only [Sym.card_coe] using Multiset.count_le_card a (s : Multiset ι)) hr
  have ht : (t : Multiset ι).count a < q :=
    lt_of_le_of_lt (by simpa only [Sym.card_coe] using Multiset.count_le_card a (t : Multiset ι)) hr
  have hv := congrArg ZMod.val hz
  simpa only [ZMod.val_natCast_of_lt hs, ZMod.val_natCast_of_lt ht] using hv

theorem multiset_phases_mean_square {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {r : ℕ} (hr : r < q) (v : Sym ι r → H) :
    (𝔼 θ : ι → ZMod q,
      ‖finitePhaseSum (fun s : Sym ι r => multisetCharacter (s : Multiset ι)) v θ‖ ^ 2) =
      ∑ s, ‖v s‖ ^ 2 :=
  additiveCharacters_mean_square _ (multisetCharacter_injective hr) v

/-- The inverse characters implement the negative phase monomials. -/
theorem negative_multiset_phases_mean_square {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {r : ℕ} (hr : r < q) (v : Sym ι r → H) :
    (𝔼 θ : ι → ZMod q,
      ‖finitePhaseSum (fun s : Sym ι r =>
        ⇑((multisetCharacter (q := q) (s : Multiset ι))⁻¹ : AddChar (ι → ZMod q) ℂ)) v θ‖ ^ 2) =
      ∑ s, ‖v s‖ ^ 2 := by
  have hinj : Function.Injective (fun s : Sym ι r =>
      (multisetCharacter (q := q) (s : Multiset ι))⁻¹) := by
    intro s t hst
    apply multisetCharacter_injective hr
    exact inv_injective hst
  exact additiveCharacters_mean_square (G := ι → ZMod q) _ hinj v

end

end KadisonKastler

end OAI
