import OAI.Analysis.MarkovType.OrderedSequences
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity.Subdivision

def skip (cut i : ℕ) : ℕ := if i < cut then i else i + 1

theorem strictMono_skip (cut : ℕ) : StrictMono (skip cut) := by
  intro i j hij
  simp only [skip]
  split_ifs <;> omega

def blockArray {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    (J : ℕ) (c : ℝ) : Fin (l + (J + r)) → ℝ :=
  Fin.append left (Fin.append (fun _ : Fin J => c / (J : ℝ)) right)

def blockVector {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    (J : ℕ) (c : ℝ) : C00 := C00.ofArray (blockArray left right J c)

private theorem place_blockArray {l r : ℕ} (left : Fin l → ℝ)
    (right : Fin r → ℝ) (J : ℕ) (c : ℝ) (g : ℕ → ℕ) :
    C00.place (fun i => g i.val) (blockArray left right J c) =
      (∑ i : Fin l, Finsupp.single (g i.val) (left i)) +
      ((∑ j : Fin J, Finsupp.single (g (l + j.val)) (c / (J : ℝ))) +
        ∑ i : Fin r, Finsupp.single (g (l + (J + i.val))) (right i)) := by
  classical
  simp only [C00.place, blockArray, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]

theorem blockVector_eq {l r : ℕ} (left : Fin l → ℝ)
    (right : Fin r → ℝ) (J : ℕ) (c : ℝ) :
    blockVector left right J c =
      (∑ i : Fin l, Finsupp.single i.val (left i)) +
      ((∑ j : Fin J, Finsupp.single (l + j.val) (c / (J : ℝ))) +
        ∑ i : Fin r, Finsupp.single (l + (J + i.val)) (right i)) := by
  exact place_blockArray left right J c id

def sample {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    (J : ℕ) (c : ℝ) (t : Fin (J + 1)) : C00 :=
  C00.place (fun i => skip (l + t.val) i.val) (blockArray left right J c)

private theorem skip_in_block {J l : ℕ} (t : Fin (J + 1)) (j : Fin J) :
    skip (l + t.val) (l + j.val) = l + (t.succAbove j).val := by
  by_cases h : j.val < t.val
  · have h' : j.castSucc < t := h
    rw [Fin.succAbove_of_castSucc_lt _ _ h']
    simp only [skip, Fin.val_castSucc]
    rw [ite_eq_left (Nat.add_lt_add_left h l)]
  · have h' : t ≤ j.castSucc := Nat.le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ h']
    simp only [skip, Fin.val_succ]
    rw [ite_eq_right (by omega)]
    omega

theorem sample_eq {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    (J : ℕ) (c : ℝ) (t : Fin (J + 1)) :
    sample left right J c t =
      (∑ i : Fin l, Finsupp.single i.val (left i)) +
      ((∑ j : Fin J,
        Finsupp.single (l + (t.succAbove j).val) (c / (J : ℝ))) +
        ∑ i : Fin r, Finsupp.single (l + (J + 1 + i.val)) (right i)) := by
  classical
  rw [sample, place_blockArray]
  have hl (i : Fin l) : skip (l + t.val) i.val = i.val := by
    apply ite_eq_left
    have hi := i.isLt
    omega
  have hr (i : Fin r) :
      skip (l + t.val) (l + (J + i.val)) = l + (J + 1 + i.val) := by
    have ht := t.isLt
    simp only [skip]
    rw [ite_eq_right (by omega)]
    omega
  simp only [hl, hr, skip_in_block]

theorem sum_deletions {A : Type*} [AddCommGroup A] (J : ℕ)
    (f : Fin (J + 1) → A) :
    (∑ t : Fin (J + 1), ∑ j : Fin J, f (t.succAbove j)) =
      J • ∑ t : Fin (J + 1), f t := by
  classical
  have hd (t : Fin (J + 1)) :
      (∑ j : Fin J, f (t.succAbove j)) = (∑ i, f i) - f t := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (Fin.sum_univ_succAbove f t).symm
  simp_rw [hd]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [add_nsmul, one_nsmul]
  abel

private theorem block_nsmul {J l : ℕ} (hJ : 0 < J) (c : ℝ) :
    J • (∑ t : Fin (J + 1), Finsupp.single (l + t.val) (c / (J : ℝ))) =
      (J + 1) •
        (∑ t : Fin (J + 1), Finsupp.single (l + t.val) (c / ((J + 1 : ℕ) : ℝ))) := by
  classical
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ]
  simp only [Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  have hj : (J : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hJ)
  have hj' : ((J + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem sum_samples {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    {J : ℕ} (hJ : 0 < J) (c : ℝ) :
    (∑ t : Fin (J + 1), sample left right J c t) =
      (J + 1) • blockVector left right (J + 1) c := by
  classical
  simp_rw [sample_eq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_deletions J (fun t : Fin (J + 1) =>
      Finsupp.single (l + t.val) (c / (J : ℝ)))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [block_nsmul hJ c, blockVector_eq]
  simp only [smul_add]

private theorem seminorm_sum_le (p : Seminorm ℝ C00) {A : Type*}
    (s : Finset A) (f : A → C00) : p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, map_zero, le_refl]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (p.add_le' _ _).trans (add_le_add le_rfl ih)

variable (p : Seminorm ℝ C00)
variable (hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
  ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a))

include hspread

theorem sample_norm {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    (J : ℕ) (c : ℝ) (t : Fin (J + 1)) :
    p (sample left right J c t) = p (blockVector left right J c) := by
  apply hspread
  intro i j hij
  exact strictMono_skip (l + t.val) (show i.val < j.val from hij)

theorem block_succ_le {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    {J : ℕ} (hJ : 0 < J) (c : ℝ) :
    p (blockVector left right (J + 1) c) ≤ p (blockVector left right J c) := by
  classical
  have h := seminorm_sum_le p Finset.univ (sample left right J c)
  rw [sum_samples left right hJ c, ← Nat.cast_smul_eq_nsmul ℝ,
    map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at h
  simp_rw [sample_norm p hspread] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < ((J + 1 : ℕ) : ℝ))).mp h

theorem block_mono {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    {J M : ℕ} (hJ : 0 < J) (hJM : J ≤ M) (c : ℝ) :
    p (blockVector left right M c) ≤ p (blockVector left right J c) := by
  induction M, hJM using Nat.le_induction with
  | base => exact le_rfl
  | succ M hJM ih =>
      exact (block_succ_le p hspread left right (by omega : 0 < M) c).trans ih

end MarkovSuperreflexivity.Subdivision

end

end OAI
