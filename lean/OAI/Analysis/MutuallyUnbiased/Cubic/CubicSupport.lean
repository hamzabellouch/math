import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

namespace OAI

/-! The common-support step of the cubic classification in §3.

These lemmas concern two three-element supports avoiding coordinate zero.
The last theorem states that a quotient having the cubed-value pattern proved
for Hadamard row ratios forces the supports to coincide.
-/

noncomputable section

namespace MUB6

def TwoValuePattern (f : (Fin 6) → ℂ) : Prop := by
  classical
  exact (∃ a b : ℂ, ∀ i, f i = a ∨ f i = b) ∧
    ∀ a : ℂ, (∃ i, f i = a) → (∃ j, f j ≠ a) →
      (Finset.univ.filter (fun i => f i = a)).card = 3

theorem value_pair_exhausts (f : (Fin 6) → ℂ)
    (hf : ∃ a b : ℂ, ∀ i, f i = a ∨ f i = b)
    (i j : (Fin 6)) (hij : f i ≠ f j) : ∀ k, f k = f i ∨ f k = f j := by
  obtain ⟨a, b, hf⟩ := hf
  rcases hf i with hi | hi
  · rcases hf j with hj | hj
    · exact False.elim (hij (hi.trans hj.symm))
    · intro k
      exact (hf k).imp (fun h => h.trans hi.symm) (fun h => h.trans hj.symm)
  · rcases hf j with hj | hj
    · intro k
      exact (hf k).symm.imp (fun h => h.trans hi.symm) (fun h => h.trans hj.symm)
    · exact False.elim (hij (hi.trans hj.symm))

theorem three_supports_have_witnesses (S U : Finset (Fin 6))
    (hS : S.card = 3) (hU : U.card = 3)
    (hS0 : (0 : (Fin 6)) ∉ S) (hU0 : (0 : (Fin 6)) ∉ U) (hne : S ≠ U) :
    (S \ U).Nonempty ∧ (U \ S).Nonempty ∧ (S ∩ U).Nonempty := by
  have hSU : (S \ U).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    apply hne
    exact Finset.eq_of_subset_of_card_le
      (Finset.sdiff_eq_empty_iff_subset.mp h) (by omega)
  have hUS : (U \ S).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    apply hne
    exact (Finset.eq_of_subset_of_card_le
      (Finset.sdiff_eq_empty_iff_subset.mp h) (by omega)).symm
  have hbound : (S ∪ U).card ≤ 5 := by
    have hsub : S ∪ U ⊆ (Finset.univ : Finset (Fin 6)).erase 0 := by
      intro i hi
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩
      intro heq
      subst i
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hS0 hi
      · exact hU0 hi
    simpa using Finset.card_le_card hsub
  have hcount : (S ∪ U).card + (S ∩ U).card = 6 := by
    simpa [hS, hU] using Finset.card_union_add_card_inter S U
  have hpos : 0 < (S ∩ U).card := by omega
  exact ⟨hSU, hUS, Finset.card_pos.mp hpos⟩

/-- For two subsets of size three in a six-element set, the number of
coordinates on which membership agrees is even, hence cannot be three. -/
theorem same_membership_card_ne_three (S U : Finset (Fin 6))
    (hS : S.card = 3) (hU : U.card = 3) :
    (Finset.univ.filter (fun i => (i ∈ S ↔ i ∈ U))).card ≠ 3 := by
  have heq : Finset.univ.filter (fun i => (i ∈ S ↔ i ∈ U)) =
      (S ∩ U) ∪ (S ∪ U)ᶜ := by
    ext i
    by_cases hs : i ∈ S <;> by_cases hu : i ∈ U <;> simp [hs, hu]
  have hdisj : Disjoint (S ∩ U) (S ∪ U)ᶜ := by
    apply Finset.disjoint_left.mpr
    intro i hi hnot
    exact (Finset.mem_compl.mp hnot)
      (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hi).1))
  have hcount : (S ∪ U).card + (S ∩ U).card = 6 := by
    simpa [hS, hU] using Finset.card_union_add_card_inter S U
  intro hbad
  rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_compl] at hbad
  change (S ∩ U).card + (6 - (S ∪ U).card) = 3 at hbad
  omega

def supportedValue (S : Finset (Fin 6)) (x : ℂ) (i : (Fin 6)) : ℂ :=
  if i ∈ S then x else 1

def supportedRatio (S U : Finset (Fin 6)) (x y : ℂ) (i : (Fin 6)) : ℂ :=
  supportedValue S x i / supportedValue U y i

/-- The exact common-support claim: a ratio of two nonconstant cubed rows
cannot have the necessary three-and-three multiplicities on distinct supports. -/
theorem common_support_of_twoValuePattern (S U : Finset (Fin 6))
    (hS : S.card = 3) (hU : U.card = 3)
    (hS0 : (0 : (Fin 6)) ∉ S) (hU0 : (0 : (Fin 6)) ∉ U)
    (x y : ℂ) (hx0 : x ≠ 0)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hp : TwoValuePattern (supportedRatio S U x y)) : S = U := by
  classical
  by_contra hne
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩, ⟨u, hu⟩⟩ :=
    three_supports_have_witnesses S U hS hU hS0 hU0 hne
  obtain ⟨hsS, hsU⟩ := Finset.mem_sdiff.mp hs
  obtain ⟨htU, htS⟩ := Finset.mem_sdiff.mp ht
  obtain ⟨huS, huU⟩ := Finset.mem_inter.mp hu
  let f := supportedRatio S U x y
  have hf0 : f 0 = 1 := by simp [f, supportedRatio, supportedValue, hS0, hU0]
  have hfs : f s = x := by simp [f, supportedRatio, supportedValue, hsS, hsU]
  have hft : f t = y⁻¹ := by simp [f, supportedRatio, supportedValue, htS, htU]
  have hfu : f u = x / y := by simp [f, supportedRatio, supportedValue, huS, huU]
  have hdist : f 0 ≠ f s := by simpa [hf0, hfs] using Ne.symm hx1
  have hvalues : ∀ i, f i = 1 ∨ f i = x := by
    simpa [hf0, hfs] using value_pair_exhausts f hp.1 0 s hdist
  have hinv : y⁻¹ = x := by
    have htvalues := hvalues t
    rw [hft] at htvalues
    exact htvalues.resolve_left (by simpa using hy1)
  have hxx : x ^ 2 = 1 ∨ x ^ 2 = x := by
    have huvalues := hvalues u
    simpa [hfu, div_eq_mul_inv, hinv, pow_two] using huvalues
  have hsq : x ^ 2 = 1 := by
    rcases hxx with h | h
    · exact h
    · have hprod : x * (x - 1) = 0 := by linear_combination h
      exact False.elim (hx1 (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hx0)))
  have hxminus : x = -1 := (sq_eq_one_iff.mp hsq).resolve_left hx1
  have hyminus : y = -1 := by
    have h := congrArg (fun z : ℂ => z⁻¹) hinv
    simpa [hxminus] using h
  have hones : (Finset.univ.filter (fun i => f i = 1)).card = 3 :=
    hp.2 1 ⟨0, hf0⟩ ⟨s, by change f s ≠ 1; rw [hfs]; exact hx1⟩
  have hset : Finset.univ.filter (fun i => f i = 1) =
      Finset.univ.filter (fun i => (i ∈ S ↔ i ∈ U)) := by
    ext i
    by_cases hs : i ∈ S <;> by_cases hu : i ∈ U <;>
      norm_num [f, supportedRatio, supportedValue, hxminus, hyminus, hs, hu]
  rw [hset] at hones
  exact same_membership_card_ne_three S U hS hU hones

end MUB6

end

end OAI
