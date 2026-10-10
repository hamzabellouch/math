import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.RuleOfSigns
import OAI.NumberTheory.Catalan.Energy.BarrierBracketRootSimplicity
import OAI.NumberTheory.Catalan.Energy.BarrierGlobalMaxReduction
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOnePointY1

namespace OAI


noncomputable section
namespace InternalCatalan
open Polynomial

theorem barrierCase1AX_transform1_signVariations :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1 / 2) (0)).signVariations = 1 := by
  rw [barrierCase1AX_transform1_eq_explicit]
  have hd : barrierCase1AXTransform1Explicit.degree = 13 := by
    unfold barrierCase1AXTransform1Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase1AXTransform1Explicit,
    List.signVariations, List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase1AX_transform1_positive_roots_le :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1 / 2) (0)).roots.countP
      (fun x => 0 < x) ≤ 1 := by
  have h := Polynomial.roots_countP_pos_le_signVariations
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1 / 2) (0))
  simpa only [barrierCase1AX_transform1_signVariations] using h

end InternalCatalan




namespace InternalCatalan
open Polynomial

theorem barrierCase1AX_transform2_signVariations :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (0) (1 / 2)).signVariations = 2 := by
  rw [barrierCase1AX_transform2_eq_explicit]
  have hd : barrierCase1AXTransform2Explicit.degree = 13 := by
    unfold barrierCase1AXTransform2Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase1AXTransform2Explicit,
    List.signVariations, List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase1AX_transform2_positive_roots_le :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (0) (1 / 2)).roots.countP
      (fun x => 0 < x) ≤ 2 := by
  have h := Polynomial.roots_countP_pos_le_signVariations
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (0) (1 / 2))
  simpa only [barrierCase1AX_transform2_signVariations] using h

end InternalCatalan




namespace InternalCatalan
open Polynomial

theorem barrierCase1AX_transform3_signVariations :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (1 / 2) (1)).signVariations = 1 := by
  rw [barrierCase1AX_transform3_eq_explicit]
  have hd : barrierCase1AXTransform3Explicit.degree = 13 := by
    unfold barrierCase1AXTransform3Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase1AXTransform3Explicit,
    List.signVariations, List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase1AX_transform3_positive_roots_le :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (1 / 2) (1)).roots.countP
      (fun x => 0 < x) ≤ 1 := by
  have h := Polynomial.roots_countP_pos_le_signVariations
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (1 / 2) (1))
  simpa only [barrierCase1AX_transform3_signVariations] using h

end InternalCatalan






namespace InternalCatalan

open Polynomial

private theorem barrierCase1AX_mapped_natDegree_le :
    (barrierCase1AX.map (Rat.castHom ℝ)).natDegree ≤ 13 := by
  calc
    _ ≤ barrierCase1AX.natDegree := Polynomial.natDegree_map_le
    _ = 13 := barrierCase1AX_natDegree

theorem barrierCase1AX_interval0_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (-1) (-1 / 2) ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 1 := by
  have hne : barrierDescartesTransform
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1) (-1 / 2) ≠ 0 := by
    intro hz
    have h := barrierCase1AX_transform0_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase1AX_transform0_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1) (-1 / 2)
      barrierCase1AX_mapped_natDegree_le hne s hs

theorem barrierCase1AX_interval1_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (-1 / 2) 0 ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 1 := by
  have hne : barrierDescartesTransform
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1 / 2) 0 ≠ 0 := by
    intro hz
    have h := barrierCase1AX_transform1_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase1AX_transform1_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1 / 2) 0
      barrierCase1AX_mapped_natDegree_le hne s hs

theorem barrierCase1AX_interval2_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo 0 (1 / 2) ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 2 := by
  have hne : barrierDescartesTransform
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 0 (1 / 2) ≠ 0 := by
    intro hz
    have h := barrierCase1AX_transform2_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase1AX_transform2_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 0 (1 / 2)
      barrierCase1AX_mapped_natDegree_le hne s hs

theorem barrierCase1AX_interval3_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (1 / 2) 1 ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 1 := by
  have hne : barrierDescartesTransform
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 (1 / 2) 1 ≠ 0 := by
    intro hz
    have h := barrierCase1AX_transform3_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase1AX_transform3_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 (1 / 2) 1
      barrierCase1AX_mapped_natDegree_le hne s hs

private theorem barrierCase1AX_map_eval_rat_ne_zero (q : ℚ)
    (hq : barrierCase1AX.eval q ≠ 0) :
    (barrierCase1AX.map (Rat.castHom ℝ)).eval (q : ℝ) ≠ 0 := by
  have heval : (barrierCase1AX.map (Rat.castHom ℝ)).eval (q : ℝ) =
      ((barrierCase1AX.eval q : ℚ) : ℝ) := by
    change (barrierCase1AX.map (Rat.castHom ℝ)).eval ((Rat.castHom ℝ) q) =
      (Rat.castHom ℝ) (barrierCase1AX.eval q)
    exact Polynomial.eval_map_apply (Rat.castHom ℝ) q
  rw [heval]
  exact_mod_cast hq

private theorem barrierCase1AX_root_subdivision {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ Set.Ioo (-1 : ℝ) (-1 / 2) ∨ x ∈ Set.Ioo (-1 / 2 : ℝ) 0 ∨
      x ∈ Set.Ioo (0 : ℝ) (1 / 2) ∨ x ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
  have hn : (barrierCase1AX.map (Rat.castHom ℝ)).eval (-1 / 2 : ℝ) ≠ 0 := by
    simpa using barrierCase1AX_map_eval_rat_ne_zero (-1 / 2)
      barrierCase1AX_subdivision_nonzero.2.1
  have hp : (barrierCase1AX.map (Rat.castHom ℝ)).eval (1 / 2 : ℝ) ≠ 0 := by
    simpa using barrierCase1AX_map_eval_rat_ne_zero (1 / 2)
      barrierCase1AX_subdivision_nonzero.2.2.2.1
  have hxne : x ≠ (-1 / 2 : ℝ) := by
    intro heq
    exact hn (by simpa only [heq] using hr)
  have hxpe : x ≠ (1 / 2 : ℝ) := by
    intro heq
    exact hp (by simpa only [heq] using hr)
  rcases hx with hx | hx
  · rcases lt_or_gt_of_ne hxne with hlt | hgt
    · exact Or.inl ⟨hx.1, hlt⟩
    · exact Or.inr (Or.inl ⟨hgt, hx.2⟩)
  · rcases lt_or_gt_of_ne hxpe with hlt | hgt
    · exact Or.inr (Or.inr (Or.inl ⟨hx.1, hlt⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hgt, hx.2⟩))

theorem barrierCase1AX_domain_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 5 := by
  classical
  let s0 := s.filter (fun x => x ∈ Set.Ioo (-1 : ℝ) (-1 / 2))
  let s1 := s.filter (fun x => x ∈ Set.Ioo (-1 / 2 : ℝ) 0)
  let s2 := s.filter (fun x => x ∈ Set.Ioo (0 : ℝ) (1 / 2))
  let s3 := s.filter (fun x => x ∈ Set.Ioo (1 / 2 : ℝ) 1)
  have h0 : s0.card ≤ 1 := by
    apply barrierCase1AX_interval0_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have h1 : s1.card ≤ 1 := by
    apply barrierCase1AX_interval1_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have h2 : s2.card ≤ 2 := by
    apply barrierCase1AX_interval2_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have h3 : s3.card ≤ 1 := by
    apply barrierCase1AX_interval3_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have hcover : s ⊆ s0 ∪ (s1 ∪ (s2 ∪ s3)) := by
    intro x hx
    have hparts := barrierCase1AX_root_subdivision (hs x hx).1 (hs x hx).2
    simp only [Finset.mem_union]
    rcases hparts with hx0 | hx1 | hx2 | hx3
    · exact Or.inl (Finset.mem_filter.mpr ⟨hx, hx0⟩)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hx, hx1⟩))
    · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hx, hx2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hx, hx3⟩)))
  calc
    s.card ≤ (s0 ∪ (s1 ∪ (s2 ∪ s3))).card := Finset.card_le_card hcover
    _ ≤ s0.card + (s1 ∪ (s2 ∪ s3)).card := Finset.card_union_le _ _
    _ ≤ s0.card + (s1.card + (s2 ∪ s3).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ s0.card + (s1.card + (s2.card + s3.card)) :=
      Nat.add_le_add_left (Nat.add_le_add_left (Finset.card_union_le _ _) _) _
    _ ≤ 1 + (1 + (2 + 1)) := Nat.add_le_add h0 (Nat.add_le_add h1 (Nat.add_le_add h2 h3))
    _ = 5 := rfl

private theorem barrierCase1X_bracket_subset_domain {m : ℤ}
    (hm : m ∈ barrierCase1XBrackets) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ha, hb, hzero⟩ := barrierCase1X_bracket_domain m hm
  have ha' : (-1 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast ha
  have hb' : (barrierBracketRight m : ℝ) < (1 : ℝ) := by exact_mod_cast hb
  rcases hzero with hneg | hpos
  · have hn' : (barrierBracketRight m : ℝ) < (0 : ℝ) := by exact_mod_cast hneg
    exact Or.inl ⟨ha'.trans hx.1, hx.2.trans hn'⟩
  · have hp' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast hpos
    exact Or.inr ⟨hp'.trans hx.1, hx.2.trans hb'⟩

private theorem barrierCase1X_brackets_disjoint {m n : ℤ}
    (hm : m ∈ barrierCase1XBrackets) (hn : n ∈ barrierCase1XBrackets)
    (hmn : m ≠ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hy : x ∈ Set.Ioo (barrierBracketLeft n : ℝ) (barrierBracketRight n : ℝ)) :
    False := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  simp only [barrierCase1XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm hn
  rcases hm with rfl | rfl | rfl | rfl | rfl
  <;> rcases hn with rfl | rfl | rfl | rfl | rfl
  all_goals try exact hmn rfl
  all_goals norm_num [barrierBracketLeft, barrierBracketRight] at hx0 hx1 hy0 hy1
  all_goals linarith

private def barrierCase1XChosenRoot (m : ℤ) : ℝ :=
  if hm : m ∈ barrierCase1XBrackets then
    Classical.choose (barrierCase1AX_root_in_each_bracket m hm)
  else 0

private theorem barrierCase1XChosenRoot_spec (m : ℤ)
    (hm : m ∈ barrierCase1XBrackets) :
    barrierCase1XChosenRoot m ∈
        Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval (barrierCase1XChosenRoot m) = 0 := by
  simpa only [barrierCase1XChosenRoot, dite_eq_left hm] using
    Classical.choose_spec (barrierCase1AX_root_in_each_bracket m hm)

private def barrierCase1XChosenRoots : Finset ℝ := by
  classical
  exact barrierCase1XBrackets.toFinset.image barrierCase1XChosenRoot

private theorem barrierCase1XChosenRoots_card : barrierCase1XChosenRoots.card = 5 := by
  classical
  have hinj : Set.InjOn barrierCase1XChosenRoot
      (↑barrierCase1XBrackets.toFinset : Set ℤ) := by
    intro m hm n hn heq
    have hm' : m ∈ barrierCase1XBrackets := List.mem_toFinset.mp hm
    have hn' : n ∈ barrierCase1XBrackets := List.mem_toFinset.mp hn
    by_contra hmn
    exact barrierCase1X_brackets_disjoint hm' hn' hmn
      (barrierCase1XChosenRoot_spec m hm').1
      (by simpa only [heq] using (barrierCase1XChosenRoot_spec n hn').1)
  unfold barrierCase1XChosenRoots
  rw [Finset.card_image_of_injOn hinj]
  norm_num [barrierCase1XBrackets]

private theorem barrierCase1XChosenRoots_spec {x : ℝ}
    (hx : x ∈ barrierCase1XChosenRoots) :
    x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 ∧ (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  change x ∈ barrierCase1XBrackets.toFinset.image barrierCase1XChosenRoot at hx
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
  have hm' : m ∈ barrierCase1XBrackets := List.mem_toFinset.mp hm
  have hr := barrierCase1XChosenRoot_spec m hm'
  exact ⟨barrierCase1X_bracket_subset_domain hm' hr.1, hr.2⟩

private theorem barrierCase1AX_root_mem_chosen {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ barrierCase1XChosenRoots := by
  classical
  by_contra hnot
  have hb : (insert x barrierCase1XChosenRoots).card ≤ 5 := by
    apply barrierCase1AX_domain_roots_card_le
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨hx, hr⟩
    · exact barrierCase1XChosenRoots_spec hy
  rw [Finset.card_insert_of_notMem hnot, barrierCase1XChosenRoots_card] at hb
  norm_num at hb

theorem barrierCase1AX_roots_exhausted {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    ∃ m ∈ barrierCase1XBrackets,
      x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) := by
  classical
  have hmem := barrierCase1AX_root_mem_chosen hx hr
  change x ∈ barrierCase1XBrackets.toFinset.image barrierCase1XChosenRoot at hmem
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hmem
  have hm' : m ∈ barrierCase1XBrackets := List.mem_toFinset.mp hm
  exact ⟨m, hm', (barrierCase1XChosenRoot_spec m hm').1⟩

theorem barrierCase1AX_unique_root_in_bracket (m : ℤ)
    (hm : m ∈ barrierCase1XBrackets) :
    ∃! x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  refine ⟨barrierCase1XChosenRoot m, barrierCase1XChosenRoot_spec m hm, ?_⟩
  intro y hy
  have hmem := barrierCase1AX_root_mem_chosen
    (barrierCase1X_bracket_subset_domain hm hy.1) hy.2
  change y ∈ barrierCase1XBrackets.toFinset.image barrierCase1XChosenRoot at hmem
  obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hmem
  have hn' : n ∈ barrierCase1XBrackets := List.mem_toFinset.mp hn
  by_cases hnm : n = m
  · subst n
    exact heq.symm
  · exact False.elim (barrierCase1X_brackets_disjoint hn' hm hnm
      (barrierCase1XChosenRoot_spec n hn').1 (by simpa only [heq] using hy.1))

end InternalCatalan




namespace InternalCatalan
open Set

theorem barrierCase1X_le_of_bracket_bounds (M : ℝ)
    (hneg : barrierCase1X (-1) ≤ M)
    (hbr : ∀ m ∈ barrierCase1XBrackets, ∀ x ∈
      Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ),
      barrierCase1X x ≤ M) :
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo (0 : ℝ) 1, barrierCase1X x ≤ M := by
  apply GlobalMaxReduction.le_on_two_components_of_stationary_cover
    (S := {x | ∃ m ∈ barrierCase1XBrackets,
      x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)})
  · intro x hx
    exact (barrierCase1X_hasDerivAt (by linarith [hx.2])
      (by linarith [hx.2])).continuousAt.continuousWithinAt
  · intro x hx
    exact (barrierCase1X_hasDerivAt (by linarith [hx.1])
      (by linarith [hx.2])).continuousAt.continuousWithinAt
  · exact hneg
  · exact barrierCase1X_tendsto_zero_left
  · exact barrierCase1X_tendsto_zero_right
  · exact barrierCase1X_tendsto_one_left
  · intro x hx hd
    have h0 : x ≠ 0 := by rcases hx with hx | hx <;> linarith [hx.1, hx.2]
    have h1 : x ≠ 1 := by rcases hx with hx | hx <;> linarith [hx.1, hx.2]
    exact barrierCase1AX_roots_exhausted hx ((barrierCase1X_deriv_eq_zero_iff h0 h1).1 hd)
  · rintro x ⟨m, hm, hx⟩
    exact hbr m hm x hx

theorem barrierCase1Y_le_of_bracket_bounds (M : ℝ)
    (hbr : ∀ m ∈ barrierCase1YBrackets, ∀ x ∈
      Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ),
      barrierCase1Y x ≤ M) :
    ∀ x ∈ Ioo (0 : ℝ) 1, barrierCase1Y x ≤ M := by
  apply GlobalMaxReduction.le_on_Ioo_of_stationary_cover
    (S := {x | ∃ m ∈ barrierCase1YBrackets,
      x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)})
  · intro x hx
    exact (barrierCase1Y_hasDerivAt (by linarith [hx.1])
      (by linarith [hx.2])).continuousAt.continuousWithinAt
  · exact barrierCase1Y_tendsto_zero_right
  · exact barrierCase1Y_tendsto_one_left
  · intro x hx hd
    exact barrierCase1AY_roots_exhausted hx ((barrierCase1Y_deriv_eq_zero_iff
      (by linarith [hx.1]) (by linarith [hx.2])).1 hd)
  · rintro x ⟨m, hm, hx⟩
    exact hbr m hm x hx

end InternalCatalan




namespace InternalCatalan
open Polynomial

private theorem rootSimplicity_case1AX_degree_le :
    (barrierCase1AX.map (Rat.castHom ℝ)).natDegree ≤ 13 :=
  Polynomial.natDegree_map_le.trans (le_of_eq barrierCase1AX_natDegree)

private theorem rootSimplicity_case1AX_interval0 {x : ℝ}
    (hx : x ∈ Set.Ioo ((-1 : ℚ) : ℝ) ((-1 / 2 : ℚ) : ℝ))
    (hp : (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase1AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  have hvar : (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ))
      13 ((-1 : ℚ) : ℝ) ((-1 / 2 : ℚ) : ℝ)).signVariations = 1 := by
    simpa using barrierCase1AX_transform0_signVariations
  have hne : barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ))
      13 ((-1 : ℚ) : ℝ) ((-1 / 2 : ℚ) : ℝ) ≠ 0 := by
    intro hz
    rw [hz, Polynomial.signVariations_zero] at hvar
    norm_num at hvar
  apply barrierDescartes_root_simple_of_brackets
    (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1) (-1 / 2) [-9917299785]
    rootSimplicity_case1AX_degree_le hne
  · decide +kernel
  · decide +kernel
  · intro m hm
    apply barrierCase1AX_root_in_each_bracket m
    have hsub : ∀ k ∈ ([-9917299785] : List ℤ), k ∈ barrierCase1XBrackets := by decide +kernel
    exact hsub m hm
  · rw [hvar]
    norm_num
  · exact hx
  · exact hp

private theorem rootSimplicity_case1AX_interval1 {x : ℝ}
    (hx : x ∈ Set.Ioo ((-1 / 2 : ℚ) : ℝ) ((0 : ℚ) : ℝ))
    (hp : (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase1AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  have hvar : (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ))
      13 ((-1 / 2 : ℚ) : ℝ) ((0 : ℚ) : ℝ)).signVariations = 1 := by
    simpa using barrierCase1AX_transform1_signVariations
  have hne : barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ))
      13 ((-1 / 2 : ℚ) : ℝ) ((0 : ℚ) : ℝ) ≠ 0 := by
    intro hz
    rw [hz, Polynomial.signVariations_zero] at hvar
    norm_num at hvar
  apply barrierDescartes_root_simple_of_brackets
    (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1 / 2) (0) [-2259572153]
    rootSimplicity_case1AX_degree_le hne
  · decide +kernel
  · decide +kernel
  · intro m hm
    apply barrierCase1AX_root_in_each_bracket m
    have hsub : ∀ k ∈ ([-2259572153] : List ℤ), k ∈ barrierCase1XBrackets := by decide +kernel
    exact hsub m hm
  · rw [hvar]
    norm_num
  · exact hx
  · exact hp

private theorem rootSimplicity_case1AX_interval2 {x : ℝ}
    (hx : x ∈ Set.Ioo ((0 : ℚ) : ℝ) ((1 / 2 : ℚ) : ℝ))
    (hp : (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase1AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  have hvar : (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ))
      13 ((0 : ℚ) : ℝ) ((1 / 2 : ℚ) : ℝ)).signVariations = 2 := by
    simpa using barrierCase1AX_transform2_signVariations
  have hne : barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ))
      13 ((0 : ℚ) : ℝ) ((1 / 2 : ℚ) : ℝ) ≠ 0 := by
    intro hz
    rw [hz, Polynomial.signVariations_zero] at hvar
    norm_num at hvar
  apply barrierDescartes_root_simple_of_brackets
    (barrierCase1AX.map (Rat.castHom ℝ)) 13 (0) (1 / 2) [2543808026, 4437270259]
    rootSimplicity_case1AX_degree_le hne
  · decide +kernel
  · decide +kernel
  · intro m hm
    apply barrierCase1AX_root_in_each_bracket m
    have hsub : ∀ k ∈ ([2543808026, 4437270259] : List ℤ), k ∈ barrierCase1XBrackets := by decide +kernel
    exact hsub m hm
  · rw [hvar]
    norm_num
  · exact hx
  · exact hp

private theorem rootSimplicity_case1AX_interval3 {x : ℝ}
    (hx : x ∈ Set.Ioo ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ))
    (hp : (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase1AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  have hvar : (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ))
      13 ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ)).signVariations = 1 := by
    simpa using barrierCase1AX_transform3_signVariations
  have hne : barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ))
      13 ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ≠ 0 := by
    intro hz
    rw [hz, Polynomial.signVariations_zero] at hvar
    norm_num at hvar
  apply barrierDescartes_root_simple_of_brackets
    (barrierCase1AX.map (Rat.castHom ℝ)) 13 (1 / 2) (1) [6348298970]
    rootSimplicity_case1AX_degree_le hne
  · decide +kernel
  · decide +kernel
  · intro m hm
    apply barrierCase1AX_root_in_each_bracket m
    have hsub : ∀ k ∈ ([6348298970] : List ℤ), k ∈ barrierCase1XBrackets := by decide +kernel
    exact hsub m hm
  · rw [hvar]
    norm_num
  · exact hx
  · exact hp

theorem barrierCase1AX_rootMultiplicity_one {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hp : (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase1AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  obtain ⟨m, hm, hb⟩ := barrierCase1AX_roots_exhausted hx hp
  simp only [barrierCase1XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · apply rootSimplicity_case1AX_interval0 (hp := hp)
    norm_num [barrierBracketLeft, barrierBracketRight] at hb ⊢
    constructor <;> linarith
  · apply rootSimplicity_case1AX_interval1 (hp := hp)
    norm_num [barrierBracketLeft, barrierBracketRight] at hb ⊢
    constructor <;> linarith
  · apply rootSimplicity_case1AX_interval2 (hp := hp)
    norm_num [barrierBracketLeft, barrierBracketRight] at hb ⊢
    constructor <;> linarith
  · apply rootSimplicity_case1AX_interval2 (hp := hp)
    norm_num [barrierBracketLeft, barrierBracketRight] at hb ⊢
    constructor <;> linarith
  · apply rootSimplicity_case1AX_interval3 (hp := hp)
    norm_num [barrierBracketLeft, barrierBracketRight] at hb ⊢
    constructor <;> linarith

theorem barrierCase1AY_rootMultiplicity_one {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hp : (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase1AY.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  have hd : (barrierCase1AY.map (Rat.castHom ℝ)).natDegree ≤ 9 :=
    Polynomial.natDegree_map_le.trans (le_of_eq barrierCase1AY_natDegree)
  have hne : barrierDescartesTransform (barrierCase1AY.map (Rat.castHom ℝ)) 9 0 1 ≠ 0 := by
    intro hz
    have h := barrierCase1AY_transform_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  have hcount : (barrierDescartesTransform (barrierCase1AY.map (Rat.castHom ℝ))
      9 0 1).signVariations ≤ barrierCase1YBrackets.toFinset.card := by
    rw [barrierCase1AY_transform_signVariations]
    norm_num [barrierCase1YBrackets]
  apply barrierDescartes_root_simple_of_brackets
    (barrierCase1AY.map (Rat.castHom ℝ)) 9 0 1 barrierCase1YBrackets hd
      (by simpa using hne)
  · decide +kernel
  · decide +kernel
  · exact barrierCase1AY_root_in_each_bracket
  · simpa using hcount
  · simpa using hx
  · exact hp

private theorem rootSimplicity_case1X_bracket_domain {m : ℤ}
    (hm : m ∈ barrierCase1XBrackets) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ha, hb, hz⟩ := barrierCase1X_bracket_domain m hm
  have ha' : (-1 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast ha
  have hb' : (barrierBracketRight m : ℝ) < (1 : ℝ) := by exact_mod_cast hb
  rcases hz with hn | hp
  · have hn' : (barrierBracketRight m : ℝ) < (0 : ℝ) := by exact_mod_cast hn
    exact Or.inl ⟨ha'.trans hx.1, hx.2.trans hn'⟩
  · have hp' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast hp
    exact Or.inr ⟨hp'.trans hx.1, hx.2.trans hb'⟩

private theorem rootSimplicity_case1Y_bracket_domain {m : ℤ}
    (hm : m ∈ barrierCase1YBrackets) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ha, hb⟩ := barrierCase1Y_bracket_domain m hm
  have ha' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast ha
  have hb' : (barrierBracketRight m : ℝ) < (1 : ℝ) := by exact_mod_cast hb
  exact ⟨ha'.trans hx.1, hx.2.trans hb'⟩

theorem barrierCase1AX_unique_simple_root_in_bracket (m : ℤ)
    (hm : m ∈ barrierCase1XBrackets) :
    ∃! x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0 ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  obtain ⟨x, hx, huniq⟩ := barrierCase1AX_unique_root_in_bracket m hm
  refine ⟨x, ⟨hx.1, hx.2, barrierCase1AX_rootMultiplicity_one
    (rootSimplicity_case1X_bracket_domain hm hx.1) hx.2⟩, ?_⟩
  intro y hy
  exact huniq y ⟨hy.1, hy.2.1⟩

theorem barrierCase1AY_unique_simple_root_in_bracket (m : ℤ)
    (hm : m ∈ barrierCase1YBrackets) :
    ∃! x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0 ∧
      (barrierCase1AY.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  obtain ⟨x, hx, huniq⟩ := barrierCase1AY_unique_root_in_bracket m hm
  refine ⟨x, ⟨hx.1, hx.2, barrierCase1AY_rootMultiplicity_one
    (rootSimplicity_case1Y_bracket_domain hm hx.1) hx.2⟩, ?_⟩
  intro y hy
  exact huniq y ⟨hy.1, hy.2.1⟩

theorem barrierCase1AX_derivative_eval_ne_zero {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hp : (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase1AX.map (Rat.castHom ℝ)).derivative.eval x ≠ 0 := by
  have hs := barrierCase1AX_rootMultiplicity_one hx hp
  have hne : barrierCase1AX.map (Rat.castHom ℝ) ≠ 0 := by
    intro hz
    simp [hz] at hs
  intro hz
  have hgt := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hne).mpr ⟨hp, hz⟩
  rw [hs] at hgt
  exact (Nat.lt_irrefl 1) hgt

theorem barrierCase1X_stationary_numerator_simple {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1) (hstat : deriv barrierCase1X x = 0) :
    (barrierCase1AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  have h0 : x ≠ 0 := by
    rcases hx with hn | hp
    · exact ne_of_lt hn.2
    · exact ne_of_gt hp.1
  have h1 : x ≠ 1 := by
    rcases hx with hn | hp
    · exact ne_of_lt (hn.2.trans (by norm_num))
    · exact ne_of_lt hp.2
  exact barrierCase1AX_rootMultiplicity_one hx
    ((barrierCase1X_deriv_eq_zero_iff h0 h1).mp hstat)

theorem barrierCase1AY_derivative_eval_ne_zero {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hp : (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0) :
    (barrierCase1AY.map (Rat.castHom ℝ)).derivative.eval x ≠ 0 := by
  have hs := barrierCase1AY_rootMultiplicity_one hx hp
  have hne : barrierCase1AY.map (Rat.castHom ℝ) ≠ 0 := by
    intro hz
    simp [hz] at hs
  intro hz
  have hgt := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hne).mpr ⟨hp, hz⟩
  rw [hs] at hgt
  exact (Nat.lt_irrefl 1) hgt

theorem barrierCase1Y_stationary_numerator_simple {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hstat : deriv barrierCase1Y x = 0) :
    (barrierCase1AY.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  have h0 : x ≠ 0 := by
    exact ne_of_gt hx.1
  have h1 : x ≠ 1 := ne_of_lt hx.2
  exact barrierCase1AY_rootMultiplicity_one hx
    ((barrierCase1Y_deriv_eq_zero_iff h0 h1).mp hstat)

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1Y2_approx_upper :
    barrierCase1YApproxRat Y2 (-1) (-2) (2850869403 / 2500000000) (2149130597 / 1250000000) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase1YApproxRat barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  norm_num [Y2, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1Y2_lt : barrierCase1Y (Y2 : ℝ) < (-14280 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1Y_approx_error Y2 (-1) (-2) (2850869403 / 2500000000) (2149130597 / 1250000000)
    Y2_normalizations.1 Y2_normalizations.2)
  have ha : ((barrierCase1YApproxRat Y2 (-1) (-2) (2850869403 / 2500000000) (2149130597 / 1250000000) : ℚ) : ℝ) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1Y2_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1Y3_approx_upper :
    barrierCase1YApproxRat Y3 (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase1YApproxRat barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  norm_num [Y3, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1Y3_lt : barrierCase1Y (Y3 : ℝ) < (-14280 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1Y_approx_error Y3 (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000)
    Y3_normalizations.1 Y3_normalizations.2)
  have ha : ((barrierCase1YApproxRat Y3 (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000) : ℚ) : ℝ) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1Y3_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1Y4_approx_upper :
    barrierCase1YApproxRat Y4 (-1) (-5) (4727245069 / 2500000000) (272754931 / 156250000) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase1YApproxRat barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  norm_num [Y4, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1Y4_lt : barrierCase1Y (Y4 : ℝ) < (-14280 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1Y_approx_error Y4 (-1) (-5) (4727245069 / 2500000000) (272754931 / 156250000)
    Y4_normalizations.1 Y4_normalizations.2)
  have ha : ((barrierCase1YApproxRat Y4 (-1) (-5) (4727245069 / 2500000000) (272754931 / 156250000) : ℚ) : ℝ) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1Y4_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan

theorem barrierCase1X_bracket_left_lt (m : ℤ)
    (hm : m ∈ barrierCase1XBrackets) :
    barrierCase1X (barrierBracketLeft m : ℝ) < (-13244 / 10000 : ℝ) := by
  simp only [barrierCase1XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · convert barrierCase1X0_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.X0]
  · convert barrierCase1X1_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.X1]
  · convert barrierCase1X2_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.X2]
  · convert barrierCase1X3_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.X3]
  · convert barrierCase1X4_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.X4]
theorem barrierCase1Y_bracket_left_lt (m : ℤ)
    (hm : m ∈ barrierCase1YBrackets) :
    barrierCase1Y (barrierBracketLeft m : ℝ) < (-14280 / 10000 : ℝ) := by
  simp only [barrierCase1YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · convert barrierCase1Y0_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.Y0]
  · convert barrierCase1Y1_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.Y1]
  · convert barrierCase1Y2_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.Y2]
  · convert barrierCase1Y3_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.Y3]
  · convert barrierCase1Y4_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.Y4]

theorem barrierCase1X_neg_one_lt : barrierCase1X (-1) < (-13244 / 10000 : ℝ) := by
  simpa [Case1PointData.X5] using barrierCase1X5_lt






theorem barrierCase1X_global_upper {x : ℝ}
    (hx : -1 ≤ x ∧ x < 1 ∧ x ≠ 0) :
    barrierCase1X x ≤ (-13244 / 10000 : ℝ) + 24 / 1000000 := by
  have hbound := barrierCase1X_le_of_bracket_bounds
    ((-13244 / 10000 : ℝ) + 24 / 1000000)
    (by linarith [barrierCase1X_neg_one_lt])
    (by
      intro m hm y hy
      have hp := barrierCase1X_bracket_left_lt m hm
      have hh := barrierCase1X_bracket_height m hm hy
      linarith)
  apply hbound x
  by_cases hneg : x < 0
  · exact Or.inl ⟨hx.1, hneg⟩
  · exact Or.inr ⟨by rcases hx with ⟨_, _, hx0⟩; rcases lt_or_gt_of_ne hx0 with h | h <;> linarith,
      hx.2.1⟩

theorem barrierCase1Y_global_upper {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    barrierCase1Y x ≤ (-14280 / 10000 : ℝ) + 24 / 1000000 := by
  apply barrierCase1Y_le_of_bracket_bounds
    ((-14280 / 10000 : ℝ) + 24 / 1000000) _ x hx
  intro m hm y hy
  have hp := barrierCase1Y_bracket_left_lt m hm
  have hh := barrierCase1Y_bracket_height m hm hy
  linarith

end InternalCatalan

end

end OAI
