import OAI.Analysis.KadisonKastler.FreeCuts
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-!
# Ordered subwords and restoration of scalar projection parts

The expansion keeps the original order of every retained subword. The
lists of subwords count choices of positions, including their multiplicity.
The resulting binomial estimate is the scalar-restoration step in §3.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

private theorem sum_map_flatMap {α β E : Type*} [AddCommMonoid E]
    (f : β → E) (g : α → List β) (l : List α) :
    ((l.flatMap g).map f).sum = (l.map (fun a => ((g a).map f).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

private theorem sum_list_range {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

section Algebra

variable {ι B : Type*} [Ring B] [Algebra ℝ B]

def orderedWord (c : ι → B) (l : List ι) : B := (l.map c).prod

def retainedSubword (c : ι → B) (s : ℝ) (r : ℕ) (l : List ι) : B :=
  s ^ (r - l.length) • orderedWord c l

/-- Expand each `c i + s • 1` by retaining a sublist of positions. -/
theorem orderedWord_add_scalar (c : ι → B) (s : ℝ) (l : List ι) :
    orderedWord (fun i => c i + s • (1 : B)) l =
      (l.sublists'.map (retainedSubword c s l.length)).sum := by
  induction l with
  | nil => simp [orderedWord, retainedSubword]
  | cons i l ih =>
    have he : (l.sublists'.map (retainedSubword c s (l.length + 1))).sum =
        s • (l.sublists'.map (retainedSubword c s l.length)).sum := by
      have ht : (l.sublists'.map (retainedSubword c s (l.length + 1))) =
          l.sublists'.map (fun k => s • retainedSubword c s l.length k) := by
        apply List.map_congr_left
        intro k hk
        have hklen := (List.mem_sublists'.mp hk).length_le
        simp only [retainedSubword, show l.length + 1 - k.length =
          (l.length - k.length) + 1 by omega, pow_succ', mul_smul]
      rw [ht]
      induction l.sublists' with
      | nil => simp
      | cons k L hL => simp only [List.map_cons, List.sum_cons, hL, smul_add]
    have hi : ((l.sublists'.map (List.cons i)).map
        (retainedSubword c s (l.length + 1))).sum =
        c i * (l.sublists'.map (retainedSubword c s l.length)).sum := by
      rw [List.map_map]
      have ht : (l.sublists'.map (retainedSubword c s (l.length + 1) ∘ List.cons i)) =
          l.sublists'.map (fun k => c i * retainedSubword c s l.length k) := by
        apply List.map_congr_left
        intro k _
        simp only [Function.comp_apply, retainedSubword, List.length_cons,
          Nat.add_sub_add_right, orderedWord, List.map_cons, List.prod_cons,
          mul_smul_comm]
      rw [ht, List.sum_map_mul_left]
    simp only [orderedWord, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, List.sublists'_cons, List.map_append, List.sum_append, List.length_cons,
      he, hi, add_mul, smul_mul_assoc, one_mul, add_comm]

/-- Group the exact ordered expansion by the number of retained positions. -/
theorem orderedWord_add_scalar_by_length (c : ι → B) (s : ℝ) (l : List ι) :
    orderedWord (fun i => c i + s • (1 : B)) l =
      ∑ k ∈ range (l.length + 1),
        ((l.sublistsLen k).map (retainedSubword c s l.length)).sum := by
  rw [orderedWord_add_scalar]
  have h := (List.range_bind_sublistsLen_perm l).map (retainedSubword c s l.length)
  rw [← h.sum_eq, sum_map_flatMap, sum_list_range]

/-- The full retained word is removed exactly; all remaining terms are proper subwords. -/
theorem orderedWord_add_scalar_sub (c : ι → B) (s : ℝ) (l : List ι) :
    orderedWord (fun i => c i + s • (1 : B)) l - orderedWord c l =
      ∑ k ∈ range l.length,
        ((l.sublistsLen k).map (retainedSubword c s l.length)).sum := by
  rw [orderedWord_add_scalar_by_length, Finset.sum_range_succ,
    List.sublistsLen_length]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    retainedSubword, Nat.sub_self, pow_zero, one_smul, add_zero, add_sub_cancel_right]

end Algebra

section Norm

variable {ι B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

omit [NormedAlgebra ℝ B] in
private theorem norm_list_sum_map_le {α : Type*} (l : List α) (f : α → B) (C : ℝ)
    (h : ∀ x ∈ l, ‖f x‖ ≤ C) : ‖(l.map f).sum‖ ≤ (l.length : ℝ) * C := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      ‖f x + (l.map f).sum‖ ≤ ‖f x‖ + ‖(l.map f).sum‖ := norm_add_le _ _
      _ ≤ C + (l.length : ℝ) * C := add_le_add (h x List.mem_cons_self)
        (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))
      _ = _ := by ring

/-- A length class contains exactly `choose r k` positional subwords. -/
theorem norm_retainedSubwords_le (c : ι → B) {d : ℝ} (hd : 0 < d)
    (l : List ι) {k : ℕ}
    (hc : ∀ w, List.Sublist w l → w.length = k →
      ‖orderedWord c w‖ ≤ (2 * k + 1 : ℝ) / Real.sqrt (d ^ (k - 1))) :
    ‖((l.sublistsLen k).map (retainedSubword c (1 / d) l.length)).sum‖ ≤
      (l.length.choose k : ℝ) *
        ((2 * k + 1 : ℝ) / (d ^ (l.length - k) * Real.sqrt (d ^ (k - 1)))) := by
  have hterm : ∀ w ∈ l.sublistsLen k,
      ‖retainedSubword c (1 / d) l.length w‖ ≤
        (2 * k + 1 : ℝ) / (d ^ (l.length - k) * Real.sqrt (d ^ (k - 1))) := by
    intro w hw
    obtain ⟨hwl, hwk⟩ := List.mem_sublistsLen.mp hw
    rw [retainedSubword, hwk, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      (1 / d) ^ (l.length - k) * ‖orderedWord c w‖ ≤
          (1 / d) ^ (l.length - k) *
            ((2 * k + 1 : ℝ) / Real.sqrt (d ^ (k - 1))) :=
        mul_le_mul_of_nonneg_left (hc w hwl hwk) (by positivity)
      _ = _ := by rw [one_div_pow]; ring
  have h := norm_list_sum_map_le (l.sublistsLen k)
    (retainedSubword c (1 / d) l.length)
    ((2 * k + 1 : ℝ) / (d ^ (l.length - k) * Real.sqrt (d ^ (k - 1)))) hterm
  simpa only [List.length_sublistsLen] using h

/-- Restoring the scalar parts of a single projection word. The only analytic
input is the proved bound for each nonempty centered subword. -/
theorem norm_orderedWord_scalar_restoration_le (c : ι → B) {d : ℝ} (hd : 0 < d)
    (hone : ‖(1 : B)‖ ≤ 1) (l : List ι) (hl : 0 < l.length)
    (hc : ∀ w, List.Sublist w l → 0 < w.length →
      ‖orderedWord c w‖ ≤
        (2 * w.length + 1 : ℝ) / Real.sqrt (d ^ (w.length - 1))) :
    ‖orderedWord (fun i => c i + (1 / d) • (1 : B)) l - orderedWord c l‖ ≤
      1 / d ^ l.length + ∑ k ∈ Ico 1 l.length, (l.length.choose k : ℝ) *
        ((2 * k + 1 : ℝ) / (d ^ (l.length - k) * Real.sqrt (d ^ (k - 1)))) := by
  have hz : ‖((l.sublistsLen 0).map
      (retainedSubword c (1 / d) l.length)).sum‖ ≤ 1 / d ^ l.length := by
    simp only [List.sublistsLen_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, retainedSubword, List.length_nil, Nat.sub_zero,
      orderedWord, List.prod_nil, norm_smul]
    rw [Real.norm_of_nonneg (pow_nonneg (one_div_nonneg.mpr hd.le) _)]
    calc
      (1 / d) ^ l.length * ‖(1 : B)‖ ≤ (1 / d) ^ l.length * 1 :=
        mul_le_mul_of_nonneg_left hone (by positivity)
      _ = _ := by rw [mul_one, one_div_pow]
  rw [orderedWord_add_scalar_sub, sum_range_eq_add_Ico _ hl]
  calc
    _ ≤ ‖((l.sublistsLen 0).map (retainedSubword c (1 / d) l.length)).sum‖ +
        ‖∑ k ∈ Ico 1 l.length,
          ((l.sublistsLen k).map (retainedSubword c (1 / d) l.length)).sum‖ :=
      norm_add_le _ _
    _ ≤ 1 / d ^ l.length + ∑ k ∈ Ico 1 l.length,
        ‖((l.sublistsLen k).map (retainedSubword c (1 / d) l.length)).sum‖ :=
      add_le_add hz (norm_sum_le _ _)
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro k hk
      have hkpos := (mem_Ico.mp hk).1
      apply norm_retainedSubwords_le c hd l
      intro w hwl hwk
      simpa only [hwk] using hc w hwl (by omega : 0 < w.length)

/-- The restoration estimate for letters already given as projections (or
any letters with the same scalar decomposition). -/
theorem norm_orderedWord_sub_centered_le (e c : ι → B) {d : ℝ} (hd : 0 < d)
    (hone : ‖(1 : B)‖ ≤ 1) (l : List ι) (hl : 0 < l.length)
    (he : ∀ i ∈ l, e i = c i + (1 / d) • (1 : B))
    (hc : ∀ w, List.Sublist w l → 0 < w.length →
      ‖orderedWord c w‖ ≤
        (2 * w.length + 1 : ℝ) / Real.sqrt (d ^ (w.length - 1))) :
    ‖orderedWord e l - orderedWord c l‖ ≤
      1 / d ^ l.length + ∑ k ∈ Ico 1 l.length, (l.length.choose k : ℝ) *
        ((2 * k + 1 : ℝ) / (d ^ (l.length - k) * Real.sqrt (d ^ (k - 1)))) := by
  have heq : orderedWord e l = orderedWord (fun i => c i + (1 / d) • (1 : B)) l := by
    unfold orderedWord
    congr 1
    exact List.map_congr_left he
  rw [heq]
  exact norm_orderedWord_scalar_restoration_le c hd hone l hl hc

/-- At most `r!` ordered tuples give the manuscript's scalar restoration bound. -/
theorem norm_sum_orderedWord_scalar_restoration_le {τ : Type*}
    (e c : ι → B) {d : ℝ} (hd : 0 < d) (hone : ‖(1 : B)‖ ≤ 1)
    (T : Finset τ) (L : τ → List ι) {r : ℕ} (hr : 0 < r)
    (hcard : T.card ≤ r.factorial)
    (hlen : ∀ t ∈ T, (L t).length = r)
    (he : ∀ t ∈ T, ∀ i ∈ L t, e i = c i + (1 / d) • (1 : B))
    (hc : ∀ t ∈ T, ∀ w, List.Sublist w (L t) → 0 < w.length →
      ‖orderedWord c w‖ ≤
        (2 * w.length + 1 : ℝ) / Real.sqrt (d ^ (w.length - 1))) :
    ‖(∑ t ∈ T, orderedWord e (L t)) - ∑ t ∈ T, orderedWord c (L t)‖ ≤
      scalarRestorationBound r d := by
  let R := 1 / d ^ r + ∑ k ∈ Ico 1 r, (r.choose k : ℝ) *
    ((2 * k + 1 : ℝ) / (d ^ (r - k) * Real.sqrt (d ^ (k - 1))))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have ht : ∀ t ∈ T, ‖orderedWord e (L t) - orderedWord c (L t)‖ ≤ R := by
    intro t ht
    have h := norm_orderedWord_sub_centered_le e c hd hone (L t)
      (by simpa only [hlen t ht] using hr) (he t ht) (hc t ht)
    simpa only [hlen t ht] using h
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ T, ‖orderedWord e (L t) - orderedWord c (L t)‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ T, R := Finset.sum_le_sum ht
    _ = (T.card : ℝ) * R := by simp
    _ ≤ (r.factorial : ℝ) * R := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hR
    _ = scalarRestorationBound r d := rfl

/-- In the creation/preservation/annihilation model, the centered-subword
input above follows directly from the exact cut decomposition. -/
theorem norm_sum_projectionWords_sub_centeredCuts_le {τ : Type*}
    (e C D A : ι → B)
    (hAC : ∀ i j, i ≠ j → A i * C j = 0)
    (hAD : ∀ i j, i ≠ j → A i * D j = 0)
    (hDC : ∀ i j, i ≠ j → D i * C j = 0)
    (hDD : ∀ i j, i ≠ j → D i * D j = 0)
    {d : ℝ} (hd : 1 ≤ d) (hone : ‖(1 : B)‖ ≤ 1)
    (hC : ∀ i, ‖C i‖ ≤ (Real.sqrt d)⁻¹)
    (hD : ∀ i, ‖D i‖ ≤ 1) (hA : ∀ i, ‖A i‖ ≤ (Real.sqrt d)⁻¹)
    (T : Finset τ) (L : τ → List ι) {r : ℕ} (hr : 0 < r)
    (hcard : T.card ≤ r.factorial) (hlen : ∀ t ∈ T, (L t).length = r)
    (hnodup : ∀ t ∈ T, (L t).Nodup)
    (he : ∀ t ∈ T, ∀ i ∈ L t, e i = C i + D i + A i + (1 / d) • (1 : B)) :
    ‖(∑ t ∈ T, orderedWord e (L t)) - ∑ t ∈ T, centeredLetterProduct C D A (L t)‖ ≤
      scalarRestorationBound r d := by
  apply norm_sum_orderedWord_scalar_restoration_le e (fun i => C i + D i + A i)
    (by linarith) hone T L hr hcard hlen he
  intro t ht w hwl _
  exact norm_centeredLetterProduct_le_inv_sqrt C D A hAC hAD hDC hDD hd hone
    hC hD hA w (List.Nodup.sublist hwl (hnodup t ht))

end Norm

end

end KadisonKastler

end OAI
