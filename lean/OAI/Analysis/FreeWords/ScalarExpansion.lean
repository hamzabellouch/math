import Mathlib

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators

noncomputable section

variable {A ι : Type*} [NormedRing A] [NormedAlgebra ℂ A]

def scalarTerm (c : ℂ) (f : ι → A) (n : ℕ) (w : List ι) : A :=
  c^(n-w.length) • (w.map f).prod

theorem prod_scalar_add (c : ℂ) (f : ι → A) (w : List ι) :
    (w.map (fun j => c • 1 + f j)).prod =
      (w.sublists'.map (scalarTerm c f w.length)).sum := by
  induction w with
  | nil => simp [scalarTerm]
  | cons j w ih =>
    rw [List.map_cons, List.prod_cons, add_mul, smul_mul_assoc, one_mul, ih,
      List.sublists'_cons, List.map_append, List.sum_append, List.map_map]
    congr 1
    · rw [List.smul_sum, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro s hs
      have hlen := (List.mem_sublists'.mp hs).length_le
      simp only [Function.comp_def, scalarTerm, List.length_cons]
      rw [show w.length+1-s.length=(w.length-s.length)+1 by omega, pow_succ', mul_smul]
    · rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro s hs
      simp only [Function.comp_def, scalarTerm, List.length_cons, Nat.add_sub_add_right,
        List.map_cons, List.prod_cons, mul_smul_comm]

omit [NormedAlgebra ℂ A] in
theorem norm_list_sum_le (L : List ι) (f : ι → A) (B : ℝ)
    (h : ∀ i ∈ L, ‖f i‖ ≤ B) : ‖(L.map f).sum‖ ≤ (L.length:ℝ)*B := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hih := ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    have hi := h i (List.mem_cons_self)
    have ht := norm_add_le (f i) ((L.map f).sum)
    nlinarith

theorem norm_scalarTerm_le {c : ℂ} {f : ι → A} {n : ℕ} {s : List ι} {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hc : ‖c‖ = t^2) (h1 : ‖(1:A)‖ ≤ 1)
    (hln : s.length < n)
    (hf : s ≠ [] → ‖(s.map f).prod‖ ≤ (3*s.length+1:ℝ)*t^(s.length-1)) :
    ‖scalarTerm c f n s‖ ≤ (3*n+1:ℝ)*t^n := by
  rw [scalarTerm, norm_smul, norm_pow, hc]
  have hn : 0 ≤ (3*n+1:ℝ) := by positivity
  by_cases hs : s = []
  · subst s
    simp only [List.length_nil, Nat.sub_zero, List.map_nil, List.prod_nil]
    have hp : (t^2)^n ≤ t^n := by
      rw [← pow_mul]
      exact pow_le_pow_of_le_one ht ht1 (by omega)
    calc
      _ ≤ (t^2)^n * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ t^n := by simpa using hp
      _ ≤ (3*n+1:ℝ)*t^n := le_mul_of_one_le_left (pow_nonneg ht _) (by nlinarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n])
  · have hlen : 1 ≤ s.length := List.length_pos_iff.mpr hs
    have hp : (t^2)^(n-s.length)*t^(s.length-1) ≤ t^n := by
      rw [← pow_mul, ← pow_add]
      exact pow_le_pow_of_le_one ht ht1 (by omega)
    calc
      _ ≤ (t^2)^(n-s.length)*((3*s.length+1:ℝ)*t^(s.length-1)) :=
        mul_le_mul_of_nonneg_left (hf hs) (by positivity)
      _ = (3*s.length+1:ℝ)*((t^2)^(n-s.length)*t^(s.length-1)) := by ring
      _ ≤ (3*n+1:ℝ)*t^n := mul_le_mul
        (by exact_mod_cast (show 3*s.length+1 ≤ 3*n+1 by omega)) hp (by positivity) hn

theorem projection_word_remainder {c : ℂ} {f : ι → A} {t : ℝ} (w : List ι)
    (hw : w.Nodup) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hc : ‖c‖ = t^2)
    (h1 : ‖(1:A)‖ ≤ 1)
    (hf : ∀ s, s.Sublist w → s ≠ [] →
      ‖(s.map f).prod‖ ≤ (3*s.length+1:ℝ)*t^(s.length-1)) :
    ‖(w.map (fun j => c • 1 + f j)).prod - (w.map f).prod‖ ≤
      (2:ℝ)^w.length*(3*w.length+1)*t^w.length := by
  classical
  let : BEq (List ι) := instBEqOfDecidableEq
  let L := w.sublists'.erase w
  have he : ((w.sublists').map (scalarTerm c f w.length)).sum =
      (w.map f).prod + (L.map (scalarTerm c f w.length)).sum := by
    simpa only [L, scalarTerm, Nat.sub_self, pow_zero, one_smul] using
      (List.sum_map_erase (scalarTerm c f w.length) (List.mem_sublists'.mpr (List.Sublist.refl w))).symm
  rw [prod_scalar_add, he, add_sub_cancel_left]
  have hB : 0 ≤ (3*w.length+1:ℝ)*t^w.length := by positivity
  calc
    _ ≤ (L.length:ℝ)*((3*w.length+1:ℝ)*t^w.length) := by
      apply norm_list_sum_le
      intro s hs
      have hmm := (List.nodup_sublists'.mpr hw).mem_erase_iff.mp hs
      have hsub := List.mem_sublists'.mp hmm.2
      have hlt : s.length < w.length := lt_of_le_of_ne hsub.length_le
        (fun heq => hmm.1 (hsub.eq_of_length heq))
      exact norm_scalarTerm_le ht ht1 hc h1 hlt (hf s hsub)
    _ ≤ (2:ℝ)^w.length*((3*w.length+1:ℝ)*t^w.length) :=
      mul_le_mul_of_nonneg_right (by
        exact_mod_cast (List.length_erase_le (a := w) (l := w.sublists')).trans_eq
          (List.length_sublists' w)) hB
    _ = _ := by ring

end

end KKFreeWords
end

end OAI
