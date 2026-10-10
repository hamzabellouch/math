import Mathlib

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.CloudRounding

open scoped BigOperators

theorem dart_rejection_count_le
    {E V A : Type*} [Fintype E] [DecidableEq A]
    (tail : E → V) (reverse : E ≃ E) (accepts : E → A → A → Bool)
    (ell : E → A) (rounded : V → A) :
    (Finset.univ.filter (fun e =>
      accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)).card ≤
    (Finset.univ.filter (fun e => accepts e (ell e) (ell (reverse e)) = false)).card +
      2 * (Finset.univ.filter (fun e => ell e ≠ rounded (tail e))).card := by
  classical
  let R : Finset E := Finset.univ.filter (fun e =>
    accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)
  let B : Finset E := Finset.univ.filter (fun e =>
    accepts e (ell e) (ell (reverse e)) = false)
  let M : Finset E := Finset.univ.filter (fun e => ell e ≠ rounded (tail e))
  let MR : Finset E := Finset.univ.filter (fun e =>
    ell (reverse e) ≠ rounded (tail (reverse e)))
  have hrev : MR.card = M.card := by
    have hsets : MR = M.map reverse.symm.toEmbedding := by
      ext e
      constructor
      · intro he
        apply Finset.mem_map.mpr
        refine ⟨reverse e, ?_, reverse.symm_apply_apply e⟩
        simpa [MR, M] using he
      · intro he
        obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
        simpa [MR, M] using hd
    rw [hsets, Finset.card_map]
  have hsub : R ⊆ (B ∪ M) ∪ MR := by
    intro e he
    by_cases hl : ell e = rounded (tail e)
    · by_cases hr : ell (reverse e) = rounded (tail (reverse e))
      · have hb : e ∈ B := by simpa [B, R, hl, hr] using he
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
      · exact Finset.mem_union_right _ (by simp [MR, hr])
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [M, hl]))
  change R.card ≤ B.card + 2 * M.card
  calc
    R.card ≤ ((B ∪ M) ∪ MR).card := Finset.card_le_card hsub
    _ ≤ (B ∪ M).card + MR.card := Finset.card_union_le _ _
    _ ≤ (B.card + M.card) + MR.card :=
      Nat.add_le_add_right (Finset.card_union_le B M) _
    _ = B.card + 2 * M.card := by rw [hrev]; omega

variable {X A D : Type*} [Fintype X] [Fintype A] [Fintype D]
variable [DecidableEq X] [DecidableEq A]

def colorSet (ell : X → A) (a : A) : Finset X :=
  Finset.univ.filter (fun x => ell x = a)

def minoritySet (ell : X → A) (m : A) : Finset X :=
  Finset.univ.filter (fun x => ell x ≠ m)

def directedCut (next : X × D → X) (S : Finset X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => xd.1 ∈ S ∧ next xd ∉ S)

def disagreementSet (ell : X → A) (next : X × D → X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => ell xd.1 ≠ ell (next xd))

abbrev Nonmajor (m : A) := {a : A // a ≠ m}

omit [DecidableEq X] in
theorem exists_max_color (ell : X → A) [Nonempty A] :
    ∃ m : A, ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun a : A => (colorSet ell a).card) Finset.univ_nonempty
  exact ⟨m, fun a => hm a (Finset.mem_univ a)⟩

noncomputable def majority (ell : X → A) [Nonempty A] : A :=
  Classical.choose (exists_max_color ell)

omit [DecidableEq X] in
theorem majority_maximal (ell : X → A) [Nonempty A] (a : A) :
    (colorSet ell a).card ≤ (colorSet ell (majority ell)).card :=
  Classical.choose_spec (exists_max_color ell) a

omit [Fintype A] in
theorem nonchosen_color_twice_le (ell : X → A) (m : A)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (a : A) (ha : a ≠ m) :
    2 * (colorSet ell a).card ≤ Fintype.card X := by
  have hd : Disjoint (colorSet ell a) (colorSet ell m) := by
    apply Finset.disjoint_left.mpr
    intro x hx hm
    have hxa : ell x = a := by simpa [colorSet] using hx
    have hxm : ell x = m := by simpa [colorSet] using hm
    exact ha (hxa.symm.trans hxm)
  have hu : (colorSet ell a).card + (colorSet ell m).card ≤ Fintype.card X := by
    calc
      _ = (colorSet ell a ∪ colorSet ell m).card :=
        (Finset.card_union_of_disjoint hd).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card X := Finset.card_univ
  have hm := maximal a
  omega

def minorityEquiv (ell : X → A) (m : A) :
    (Σ a : Nonmajor m, ↥(colorSet ell a.val)) ≃ ↥(minoritySet ell m) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val = t.1.val := (Finset.mem_filter.mp t.2.property).2
    have hn : ell t.2.val ≠ m := fun h => t.1.property (hc.symm.trans h)
    simpa [minoritySet] using hn⟩
  invFun x :=
    ⟨⟨ell x.val, by simpa [minoritySet] using x.property⟩,
      ⟨x.val, by simp [colorSet]⟩⟩
  left_inv t := by
    rcases t with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    have hxa : ell x = a := by simpa [colorSet] using hx
    cases hxa
    rfl
  right_inv x := by apply Subtype.ext; rfl

omit [DecidableEq X] in
theorem minority_card_eq_sum (ell : X → A) (m : A) :
    (minoritySet ell m).card = ∑ a : Nonmajor m, (colorSet ell a.val).card := by
  have h := Fintype.card_congr (minorityEquiv ell m)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

def minorityCutEmbedding (ell : X → A) (next : X × D → X) (m : A) :
    (Σ a : Nonmajor m, ↥(directedCut next (colorSet ell a.val))) ↪
      ↥(disagreementSet ell next) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val.1 = t.1.val ∧ ell (next t.2.val) ≠ t.1.val := by
      simpa [directedCut, colorSet] using t.2.property
    have hn : ell t.2.val.1 ≠ ell (next t.2.val) :=
      fun h => hc.2 (h.symm.trans hc.1)
    simpa [disagreementSet] using hn⟩
  inj' p q h := by
    rcases p with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    rcases q with ⟨⟨b, hb⟩, ⟨y, hy⟩⟩
    have hxy : x = y := congrArg Subtype.val h
    cases hxy
    have hxa : ell x.1 = a := by
      have hc : ell x.1 = a ∧ ell (next x) ≠ a := by
        simpa [directedCut, colorSet] using hx
      exact hc.1
    have hxb : ell x.1 = b := by
      have hc : ell x.1 = b ∧ ell (next x) ≠ b := by
        simpa [directedCut, colorSet] using hy
      exact hc.1
    have hab : a = b := hxa.symm.trans hxb
    cases hab
    rfl

theorem minority_cut_sum_le (ell : X → A) (next : X × D → X) (m : A) :
    (∑ a : Nonmajor m, (directedCut next (colorSet ell a.val)).card) ≤
      (disagreementSet ell next).card := by
  have h := Fintype.card_le_of_injective
    (minorityCutEmbedding ell next m) (minorityCutEmbedding ell next m).injective
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h

theorem minority_expansion_bound (ell : X → A) (next : X × D → X) (m : A)
    (h : ℚ)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (expansion : ∀ S : Finset X, S.card ≤ Fintype.card X / 2 →
      h * (S.card : ℚ) ≤ ((directedCut next S).card : ℚ)) :
    h * ((minoritySet ell m).card : ℚ) ≤ ((disagreementSet ell next).card : ℚ) := by
  have each (a : Nonmajor m) :
      h * ((colorSet ell a.val).card : ℚ) ≤
        ((directedCut next (colorSet ell a.val)).card : ℚ) := by
    apply expansion
    have ha := nonchosen_color_twice_le ell m maximal a.val a.property
    omega
  calc
    h * ((minoritySet ell m).card : ℚ) =
        ∑ a : Nonmajor m, h * ((colorSet ell a.val).card : ℚ) := by
      rw [minority_card_eq_sum, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ a : Nonmajor m, ((directedCut next (colorSet ell a.val)).card : ℚ) :=
      Finset.sum_le_sum (fun a _ => each a)
    _ ≤ ((disagreementSet ell next).card : ℚ) := by
      exact_mod_cast minority_cut_sum_le ell next m

end IndependentSetsGames.Foundations.PCP.CloudRounding

end OAI
