import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LengthPolynomial

namespace OAI

namespace BlueSubsetDP
open Finset
variable {L : Type*} [DecidableEq L]

def blocks (U : Finset L) : Finset (Finset L) := U.powerset.erase ∅

lemma mem_blocks {U V : Finset L} : V ∈ blocks U ↔ V.Nonempty ∧ V ⊆ U := by
  simp [blocks, Finset.nonempty_iff_ne_empty]

inductive Partition : Finset L → List (Finset L) → Prop
  | nil : Partition ∅ []
  | cons {U V : Finset L} {P : List (Finset L)}
      (hne : V.Nonempty) (hsub : V ⊆ U) (tail : Partition (U \ V) P) :
      Partition U (V :: P)

lemma Partition.subset {U : Finset L} {P : List (Finset L)}
    (h : Partition U P) : ∀ V ∈ P, V ⊆ U := by
  induction h with
  | nil => simp
  | cons hne hsub tail ih =>
    intro W hW
    rcases List.mem_cons.mp hW with rfl | hW
    · exact hsub
    · exact (ih _ hW).trans Finset.sdiff_subset

lemma Partition.nonempty {U : Finset L} {P : List (Finset L)}
    (h : Partition U P) : ∀ V ∈ P, V.Nonempty := by
  induction h with
  | nil => simp
  | cons hne hsub tail ih =>
    intro W hW
    rcases List.mem_cons.mp hW with rfl | hW
    · exact hne
    · exact ih _ hW

lemma Partition.pairwise {U : Finset L} {P : List (Finset L)}
    (h : Partition U P) : P.Pairwise Disjoint := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @cons U V P hne hsub tail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro W hW
    exact Finset.disjoint_left.mpr (fun x hxV hxW =>
      (Finset.mem_sdiff.mp (tail.subset W hW hxW)).2 hxV)

lemma Partition.union {U : Finset L} {P : List (Finset L)}
    (h : Partition U P) : P.foldr (· ∪ ·) ∅ = U := by
  induction h with
  | nil => rfl
  | @cons U V P hne hsub tail ih =>
    simp only [List.foldr_cons, ih]
    exact Finset.union_sdiff_of_subset hsub

lemma Partition.length_le {U : Finset L} {P : List (Finset L)}
    (h : Partition U P) : P.length ≤ U.card := by
  induction h with
  | nil => simp
  | @cons U V P hne hsub tail ih =>
    have hcard := Finset.card_sdiff_add_card_eq_card hsub
    have hv := hne.card_pos
    simp only [List.length_cons]
    omega

noncomputable def value (C : Finset L → WithTop ℝ) : ℕ → Finset L → WithTop ℝ
  | 0, U => if U = ∅ then 0 else ⊤
  | t + 1, U => (blocks U).inf (fun V => C V + value C t (U \ V))

lemma value_zero (C : Finset L → WithTop ℝ) : value C 0 ∅ = 0 := by
  simp [value]

lemma value_le_partition (C : Finset L → WithTop ℝ) {U : Finset L}
    {P : List (Finset L)} (h : Partition U P) :
    value C P.length U ≤ (P.map C).sum := by
  induction h with
  | nil => simp [value]
  | @cons U V P hne hsub tail ih =>
    simp only [List.length_cons, value, List.map_cons, List.sum_cons]
    exact (Finset.inf_le (mem_blocks.mpr ⟨hne, hsub⟩)).trans (add_le_add (le_refl _) ih)

lemma value_attained (C : Finset L → WithTop ℝ) (t : ℕ) (U : Finset L)
    (hfin : value C t U ≠ ⊤) :
    ∃ P, Partition U P ∧ P.length = t ∧ (P.map C).sum = value C t U := by
  induction t generalizing U with
  | zero =>
    have hu : U = ∅ := by
      by_contra hn
      exact hfin (by simp [value, hn])
    subst U
    exact ⟨[], Partition.nil, rfl, by simp [value]⟩
  | succ t ih =>
    have hb : (blocks U).Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      exact hfin (by simp [value, he])
    obtain ⟨V, hV, hv⟩ := Finset.exists_mem_eq_inf (blocks U) hb
      (fun V => C V + value C t (U \ V))
    change value C (t + 1) U = C V + value C t (U \ V) at hv
    have htail : value C t (U \ V) ≠ ⊤ := by
      intro ht
      apply hfin
      simp [hv, ht]
    obtain ⟨P, hP, hlen, heq⟩ := ih (U \ V) htail
    refine ⟨V :: P, Partition.cons (mem_blocks.mp hV).1 (mem_blocks.mp hV).2 hP,
      by simp [hlen], ?_⟩
    simp only [List.map_cons, List.sum_cons, heq, ← hv]

lemma value_le_iff_partition (C : Finset L → WithTop ℝ) (t : ℕ) (U : Finset L)
    (x : ℝ) : value C t U ≤ x ↔
      ∃ P, Partition U P ∧ P.length = t ∧ (P.map C).sum ≤ (x : WithTop ℝ) := by
  constructor
  · intro h
    have hn : value C t U ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top h
    obtain ⟨P, hP, hlen, heq⟩ := value_attained C t U hn
    exact ⟨P, hP, hlen, heq ▸ h⟩
  · rintro ⟨P, hP, rfl, h⟩
    exact (value_le_partition C hP).trans h

noncomputable def best (C : Finset L → WithTop ℝ) (c : ℕ) (U : Finset L) : WithTop ℝ :=
  if U = ∅ then 0 else (Finset.Icc 1 c).inf (fun t => value C t U)

lemma best_attained (C : Finset L → WithTop ℝ) (c : ℕ) (U : Finset L)
    (hfin : best C c U ≠ ⊤) :
    ∃ P, Partition U P ∧ P.length ≤ c ∧ (P.map C).sum = best C c U := by
  by_cases hu : U = ∅
  · subst U
    exact ⟨[], Partition.nil, by simp, by simp [best]⟩
  · have hi : (Finset.Icc 1 c).Nonempty := by
      by_contra hn
      exact hfin (by simp [best, hu, Finset.not_nonempty_iff_eq_empty.mp hn])
    obtain ⟨t, ht, heq⟩ := Finset.exists_mem_eq_inf (Finset.Icc 1 c) hi
      (fun t => value C t U)
    have he : best C c U = value C t U := by simp [best, hu, heq]
    obtain ⟨P, hP, hlen, hval⟩ := value_attained C t U (he ▸ hfin)
    exact ⟨P, hP, hlen ▸ (Finset.mem_Icc.mp ht).2, by simpa [he] using hval⟩

lemma best_le_partition (C : Finset L → WithTop ℝ) (c : ℕ) {U : Finset L}
    {P : List (Finset L)} (hP : Partition U P) (hlen : P.length ≤ c) :
    best C c U ≤ (P.map C).sum := by
  by_cases hu : U = ∅
  · have hp : P = [] := List.length_eq_zero_iff.mp (by
      have := hP.length_le
      simpa [hu] using this)
    simp [best, hu, hp]
  · have hp : 0 < P.length := by
      by_contra hn
      have he : P = [] := List.length_eq_zero_iff.mp (by omega)
      have := hP.union
      simp [he] at this
      exact hu this.symm
    simp only [best, hu, ↓reduceIte]
    exact (Finset.inf_le (Finset.mem_Icc.mpr ⟨hp, hlen⟩)).trans (value_le_partition C hP)

variable {R Y : Type*} [DecidableEq R] [DecidableEq Y]

noncomputable def blockCost (B : Finset R) (F : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (U : Finset L) : WithTop ℝ :=
  F.inf (fun y => ∑ l ∈ U, (B.filter (label · = l)).inf (fun r => (q r y : WithTop ℝ)))

omit [DecidableEq R] [DecidableEq Y] in
lemma blockCost_le (B : Finset R) (F : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (U : Finset L) (y : Y) (hy : y ∈ F) (sel : L → R)
    (hsel : ∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l) :
    blockCost B F label q U ≤ (∑ l ∈ U, q (sel l) y : ℝ) := by
  unfold blockCost
  refine (Finset.inf_le hy).trans ?_
  rw [WithTop.coe_sum]
  apply Finset.sum_le_sum
  intro l hl
  exact Finset.inf_le (Finset.mem_filter.mpr (hsel l hl))

omit [DecidableEq R] [DecidableEq Y] in
lemma blockCost_attained [Nonempty R] (B : Finset R) (F : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (U : Finset L) (h : blockCost B F label q U ≠ ⊤) :
    ∃ y ∈ F, ∃ sel : L → R, (∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l) ∧
      blockCost B F label q U = (∑ l ∈ U, q (sel l) y : ℝ) := by
  have hF : F.Nonempty := by
    by_contra hn
    exact h (by simp [blockCost, Finset.not_nonempty_iff_eq_empty.mp hn])
  obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_inf F hF
    (fun y => ∑ l ∈ U, (B.filter (label · = l)).inf (fun r => (q r y : WithTop ℝ)))
  change blockCost B F label q U = _ at he
  have hlab : ∀ l ∈ U, ∃ r ∈ B, label r = l ∧
      (B.filter (label · = l)).inf (fun r => (q r y : WithTop ℝ)) = q r y := by
    intro l hl
    have hn : (B.filter (label · = l)).inf (fun r => (q r y : WithTop ℝ)) ≠ ⊤ :=
      WithTop.sum_ne_top.mp (he ▸ h) l hl
    have hb : (B.filter (label · = l)).Nonempty := by
      by_contra hh
      exact hn (by simp [Finset.not_nonempty_iff_eq_empty.mp hh])
    obtain ⟨r, hr, hmin⟩ := Finset.exists_mem_eq_inf _ hb (fun r => (q r y : WithTop ℝ))
    exact ⟨r, (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2, hmin⟩
  classical
  let sel : L → R := fun l => if hl : l ∈ U then (hlab l hl).choose else Classical.choice ‹Nonempty R›
  have hs : ∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l ∧
      (B.filter (label · = l)).inf (fun r => (q r y : WithTop ℝ)) = q (sel l) y := by
    intro l hl
    simpa only [sel, dite_eq_left hl] using (hlab l hl).choose_spec
  refine ⟨y, hy, sel, fun l hl => ⟨(hs l hl).1, (hs l hl).2.1⟩, ?_⟩
  rw [he, WithTop.coe_sum]
  exact Finset.sum_congr rfl (fun l hl => (hs l hl).2.2)

lemma Partition.cost_sum {U : Finset L} {P : List (Finset L)} (h : Partition U P)
    {M : Type*} [AddCommMonoid M] (q : L → M) :
    (P.map (fun V => ∑ l ∈ V, q l)).sum = ∑ l ∈ U, q l := by
  induction h with
  | nil => simp
  | @cons U V P hne hsub tail ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simpa only [add_comm] using Finset.sum_sdiff hsub (f := q)

lemma partition_by_destination (U : Finset L) (dst : L → Y) :
    ∃ P, Partition U P ∧ P.length ≤ (U.image dst).card ∧
      ∀ V ∈ P, ∃ y, ∀ l ∈ V, dst l = y := by
  classical
  refine Finset.strongInductionOn U ?_
  intro U ih
  by_cases he : U = ∅
  · subst U
    exact ⟨[], Partition.nil, by simp, by simp⟩
  obtain ⟨l₀, hl₀⟩ := Finset.nonempty_iff_ne_empty.mpr he
  let V := U.filter (fun l => dst l = dst l₀)
  have hlV : l₀ ∈ V := by simp [V, hl₀]
  have hV : V.Nonempty := ⟨l₀, hlV⟩
  have hVU : V ⊆ U := Finset.filter_subset _ _
  have hss : U \ V ⊂ U := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.sdiff_subset, fun hh => (Finset.mem_sdiff.mp (hh ▸ hl₀)).2 hlV⟩
  obtain ⟨P, hP, hlen, hconst⟩ := ih _ hss
  have himage : (U \ V).image dst ⊆ (U.image dst).erase (dst l₀) := by
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hy
    rcases Finset.mem_sdiff.mp hl with ⟨hlU, hlV'⟩
    exact Finset.mem_erase.mpr ⟨fun hh => hlV' (Finset.mem_filter.mpr ⟨hlU, hh⟩),
      Finset.mem_image.mpr ⟨l, hlU, rfl⟩⟩
  have hc := Finset.card_le_card himage
  have hecard := Finset.card_erase_add_one (Finset.mem_image.mpr ⟨l₀, hl₀, rfl⟩ : dst l₀ ∈ U.image dst)
  refine ⟨V :: P, Partition.cons hV hVU hP, by simp only [List.length_cons]; omega, ?_⟩
  intro W hW
  rcases List.mem_cons.mp hW with rfl | hW
  · exact ⟨dst l₀, fun l hl => (Finset.mem_filter.mp hl).2⟩
  · exact hconst _ hW
omit [DecidableEq R] in

lemma best_le_routing (B : Finset R) (F : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (U : Finset L) (c : ℕ) (sel : L → R) (dst : L → Y)
    (hsel : ∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l)
    (hdst : ∀ l ∈ U, dst l ∈ F) (hcount : (U.image dst).card ≤ c) :
    best (blockCost B F label q) c U ≤ (∑ l ∈ U, q (sel l) (dst l) : ℝ) := by
  obtain ⟨P, hP, hlen, hconst⟩ := partition_by_destination U dst
  refine (best_le_partition _ _ hP (hlen.trans hcount)).trans ?_
  rw [WithTop.coe_sum, ← hP.cost_sum (fun l => (q (sel l) (dst l) : WithTop ℝ))]
  apply List.sum_le_sum
  intro V hV
  obtain ⟨y, hy⟩ := hconst V hV
  obtain ⟨l₀, hl₀⟩ := hP.nonempty V hV
  have hyF : y ∈ F := hy l₀ hl₀ ▸ hdst l₀ (hP.subset V hV hl₀)
  calc
    blockCost B F label q V ≤ (∑ l ∈ V, q (sel l) y : ℝ) :=
      blockCost_le B F label q V y hyF sel (fun l hl => hsel l (hP.subset V hV hl))
    _ = ∑ l ∈ V, (q (sel l) (dst l) : WithTop ℝ) := by
      rw [WithTop.coe_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [hy l hl]

omit [DecidableEq R] in
lemma partition_routing [Nonempty R] [Nonempty Y]
    (B : Finset R) (F : Finset Y) (label : R → L) (q : R → Y → ℝ)
    {U : Finset L} {P : List (Finset L)} (hP : Partition U P)
    (hfin : (P.map (blockCost B F label q)).sum ≠ ⊤) :
    ∃ sel : L → R, ∃ dst : L → Y,
      (∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l ∧ dst l ∈ F) ∧
      (U.image dst).card ≤ P.length ∧
      ((∑ l ∈ U, q (sel l) (dst l) : ℝ) : WithTop ℝ) =
        (P.map (blockCost B F label q)).sum := by
  classical
  induction hP with
  | nil =>
    exact ⟨fun _ => Classical.choice ‹Nonempty R›, fun _ => Classical.choice ‹Nonempty Y›,
      by simp, by simp, by simp⟩
  | @cons U V P hne hsub tail ih =>
    simp only [List.map_cons, List.sum_cons] at hfin ⊢
    obtain ⟨y, hy, sel₁, hs₁, hcost₁⟩ := blockCost_attained B F label q V
      (WithTop.add_ne_top.mp hfin).1
    obtain ⟨sel₂, dst₂, hs₂, hcard₂, hcost₂⟩ := ih (WithTop.add_ne_top.mp hfin).2
    let sel : L → R := fun l => if l ∈ V then sel₁ l else sel₂ l
    let dst : L → Y := fun l => if l ∈ V then y else dst₂ l
    have hs : ∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l ∧ dst l ∈ F := by
      intro l hl
      by_cases hv : l ∈ V
      · simpa only [sel, dst, ite_eq_left hv] using ⟨(hs₁ l hv).1, (hs₁ l hv).2, hy⟩
      · simpa only [sel, dst, ite_eq_right hv] using hs₂ l (Finset.mem_sdiff.mpr ⟨hl, hv⟩)
    have himage : U.image dst ⊆ insert y ((U \ V).image dst₂) := by
      intro z hz
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
      by_cases hv : l ∈ V
      · simp [dst, hv]
      · exact Finset.mem_insert_of_mem (by
          simpa only [dst, ite_eq_right hv] using Finset.mem_image.mpr
            ⟨l, Finset.mem_sdiff.mpr ⟨hl, hv⟩, rfl⟩)
    have hcard : (U.image dst).card ≤ (V :: P).length := by
      have h₁ := Finset.card_le_card himage
      have h₂ := Finset.card_insert_le y ((U \ V).image dst₂)
      simp only [List.length_cons]
      omega
    refine ⟨sel, dst, hs, hcard, ?_⟩
    have hvsum : ∑ l ∈ V, q (sel l) (dst l) = ∑ l ∈ V, q (sel₁ l) y := by
      apply Finset.sum_congr rfl
      intro l hl
      simp only [sel, dst, ite_eq_left hl]
    have hrest : ∑ l ∈ U \ V, q (sel l) (dst l) =
        ∑ l ∈ U \ V, q (sel₂ l) (dst₂ l) := by
      apply Finset.sum_congr rfl
      intro l hl
      simp only [sel, dst, ite_eq_right (Finset.mem_sdiff.mp hl).2]
    rw [← Finset.sum_sdiff hsub, WithTop.coe_add, hrest, hvsum, hcost₂, ← hcost₁, add_comm]

lemma best_routing [Nonempty R] [Nonempty Y]
    (B : Finset R) (F : Finset Y) (label : R → L) (q : R → Y → ℝ)
    (U : Finset L) (c : ℕ) (hfin : best (blockCost B F label q) c U ≠ ⊤) :
    ∃ sel : L → R, ∃ dst : L → Y,
      (∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l ∧ dst l ∈ F) ∧
      (U.image sel).card = U.card ∧ (U.image dst).card ≤ c ∧
      ((∑ l ∈ U, q (sel l) (dst l) : ℝ) : WithTop ℝ) = best (blockCost B F label q) c U := by
  obtain ⟨P, hP, hlen, he⟩ := best_attained (blockCost B F label q) c U hfin
  obtain ⟨sel, dst, hs, hc, hcost⟩ := partition_routing B F label q hP (he ▸ hfin)
  refine ⟨sel, dst, hs, ?_, hc.trans hlen, hcost.trans he⟩
  apply Finset.card_image_of_injOn
  intro l hl l' hl' hh
  exact ((hs l hl).2.1).symm.trans ((congrArg label hh).trans (hs l' hl').2.1)

omit [DecidableEq R] [DecidableEq Y] in

lemma layer_transition_bound (U : Finset L) :
    ∑ V ∈ U.powerset, (blocks V).card ≤ 3 ^ U.card := by
  have hsum : ∑ V ∈ U.powerset, 2 ^ V.card = (3 : ℕ) ^ U.card := by
    simpa using (Finset.prod_one_add (f := fun _ : L => (2 : ℕ)) U).symm
  rw [← hsum]
  apply Finset.sum_le_sum
  intro V _
  rw [← Finset.card_powerset]
  exact Finset.card_le_card (Finset.erase_subset _ _)

omit [DecidableEq R] [DecidableEq Y] in
lemma all_layers_transition_bound (U : Finset L) (c : ℕ) :
    c * (∑ V ∈ U.powerset, (blocks V).card) ≤ c * 3 ^ U.card :=
  Nat.mul_le_mul_left c (layer_transition_bound U)

end BlueSubsetDP

end OAI
