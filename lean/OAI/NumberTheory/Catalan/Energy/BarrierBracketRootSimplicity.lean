import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Filter
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOneDescartesX0

namespace OAI

noncomputable section
namespace InternalCatalan
open Polynomial

private theorem rootSimplicity_right_le_left {m n : ℤ} (h : m + 2 ≤ n) :
    (barrierBracketRight m : ℝ) ≤ (barrierBracketLeft n : ℝ) := by
  have hq : barrierBracketRight m ≤ barrierBracketLeft n := by
    unfold barrierBracketRight barrierBracketLeft
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num)
  exact_mod_cast hq

theorem barrierDescartes_root_simple_of_brackets
    (p : ℝ[X]) (d : ℕ) (a b : ℚ) (B : List ℤ)
    (hd : p.natDegree ≤ d)
    (hne : barrierDescartesTransform p d (a : ℝ) (b : ℝ) ≠ 0)
    (hsep : ∀ m ∈ B, ∀ n ∈ B, m ≠ n → m + 2 ≤ n ∨ n + 2 ≤ m)
    (hinside : ∀ m ∈ B, a ≤ barrierBracketLeft m ∧ barrierBracketRight m ≤ b)
    (hex : ∀ m ∈ B, ∃ x : ℝ,
      x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
        p.eval x = 0)
    (hcount : (barrierDescartesTransform p d (a : ℝ) (b : ℝ)).signVariations ≤
      B.toFinset.card)
    {x : ℝ} (hx : x ∈ Set.Ioo (a : ℝ) (b : ℝ)) (hp : p.eval x = 0) :
    p.rootMultiplicity x = 1 := by
  classical
  let Q := barrierDescartesTransform p d (a : ℝ) (b : ℝ)
  let M := Q.roots.filter (fun t : ℝ => 0 < t)
  let f : ℤ → ℝ := fun m => if hm : m ∈ B then Classical.choose (hex m hm) else 0
  have hf (m : ℤ) (hm : m ∈ B) :
      f m ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
        p.eval (f m) = 0 := by
    simpa only [f, dite_eq_left hm] using Classical.choose_spec (hex m hm)
  have hfi (m : ℤ) (hm : m ∈ B) : f m ∈ Set.Ioo (a : ℝ) (b : ℝ) := by
    have hl : (a : ℝ) ≤ (barrierBracketLeft m : ℝ) := by
      exact_mod_cast (hinside m hm).1
    have hr : (barrierBracketRight m : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (hinside m hm).2
    exact ⟨hl.trans_lt (hf m hm).1.1, (hf m hm).1.2.trans_le hr⟩
  let T : ℝ → ℝ := fun y => (y - (a : ℝ)) / ((b : ℝ) - y)
  have hcard : B.toFinset.card ≤ M.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun m : ℤ => T (f m))
    · intro m hm
      have hm' : m ∈ B := List.mem_toFinset.mp hm
      obtain ⟨ht, hroot⟩ := barrierDescartesTransform_root_of_interval p d hd
        (hfi m hm') (hf m hm').2
      exact Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr
        ⟨(Polynomial.mem_roots hne).mpr hroot, ht⟩)
    · intro m hm n hn heq
      have hm' : m ∈ B := List.mem_toFinset.mp hm
      have hn' : n ∈ B := List.mem_toFinset.mp hn
      have hfm : f m = f n := by
        have hi := (barrierMobius_inverse (hfi m hm')).2
        have hj := (barrierMobius_inverse (hfi n hn')).2
        change T (f m) = T (f n) at heq
        change ((a : ℝ) + (b : ℝ) * T (f m)) / (1 + T (f m)) = f m at hi
        change ((a : ℝ) + (b : ℝ) * T (f n)) / (1 + T (f n)) = f n at hj
        exact hi.symm.trans ((congrArg
          (fun t : ℝ => ((a : ℝ) + (b : ℝ) * t) / (1 + t)) heq).trans hj)
      by_contra hmn
      rcases hsep m hm' n hn' hmn with hmn' | hnm'
      · have hs := rootSimplicity_right_le_left hmn'
        have hlt : (barrierBracketLeft n : ℝ) < (barrierBracketRight m : ℝ) := by
          exact (hf n hn').1.1.trans (by simpa only [hfm] using (hf m hm').1.2)
        exact (not_lt_of_ge hs) hlt
      · have hs := rootSimplicity_right_le_left hnm'
        have hlt : (barrierBracketLeft m : ℝ) < (barrierBracketRight n : ℝ) := by
          exact (hf m hm').1.1.trans (by simpa only [hfm] using (hf n hn').1.2)
        exact (not_lt_of_ge hs) hlt
  have hupper : M.card ≤ Q.signVariations := by
    simpa only [M, Multiset.countP_eq_card_filter] using
      Polynomial.roots_countP_pos_le_signVariations Q
  have hnodup : M.Nodup :=
    Multiset.toFinset_card_eq_card_iff_nodup.mp
      (Nat.le_antisymm (Multiset.toFinset_card_le M) ((hupper.trans hcount).trans hcard))
  obtain ⟨ht, hroot⟩ := barrierDescartesTransform_root_of_interval p d hd hx hp
  have hmem : T x ∈ M := Multiset.mem_filter.mpr
    ⟨(Polynomial.mem_roots hne).mpr hroot, ht⟩
  have hsimple : Q.rootMultiplicity (T x) = 1 := by
    calc
      Q.rootMultiplicity (T x) = Q.roots.count (T x) := (Polynomial.count_roots Q).symm
      _ = M.count (T x) := (Multiset.count_filter_of_pos ht).symm
      _ = 1 := Multiset.count_eq_one_of_mem hnodup hmem
  exact barrierDescartesTransform_rootMultiplicity_one_of_interval p d hd hx hp hsimple

end InternalCatalan

end

end OAI
