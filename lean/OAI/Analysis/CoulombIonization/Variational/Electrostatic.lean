import Mathlib
import OAI.Analysis.CoulombIonization.Model

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

lemma triangular_sum_eq_half {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hs : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, if j < i then f i j else 0) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, if i ≠ j then f i j else 0 := by
  classical
  have he : (∑ i, ∑ j, if i < j then f i j else 0) =
      ∑ i, ∑ j, if j < i then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  have ht (i j : ι) : (if j < i then f i j else 0) +
      (if i < j then f i j else 0) = if i ≠ j then f i j else 0 := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst j; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have hh : (∑ i, ∑ j, if j < i then f i j else 0) +
      (∑ i, ∑ j, if i < j then f i j else 0) =
      ∑ i, ∑ j, if i ≠ j then f i j else 0 := by
    simp only [← Finset.sum_add_distrib, ht]
  rw [he] at hh
  linarith

def pairPotential {N : ℕ} (x : Configuration N) : ℝ :=
  ∑ i, ∑ j, if j < i then 1 / ‖x i - x j‖ else 0

lemma pairPotential_perm {N : ℕ} (x : Configuration N) (σ : Equiv.Perm (Fin N)) :
    pairPotential (x ∘ σ) = pairPotential x := by
  classical
  have hs (y : Configuration N) (i j : Fin N) :
      1 / ‖y i - y j‖ = 1 / ‖y j - y i‖ := by rw [norm_sub_rev]
  unfold pairPotential
  rw [triangular_sum_eq_half _ (hs _), triangular_sum_eq_half _ (hs _)]
  congr 1
  have ht (i j : Fin N) : (if i ≠ j then 1 / ‖(x ∘ σ) i - (x ∘ σ) j‖ else 0) =
      if σ i ≠ σ j then 1 / ‖x (σ i) - x (σ j)‖ else 0 := by
    simp only [ne_eq, σ.injective.eq_iff, Function.comp_apply]
  simp only [ht]
  rw [show (∑ i : Fin N, ∑ j : Fin N, if σ i ≠ σ j then 1 / ‖x (σ i) - x (σ j)‖ else 0) =
      (∑ i : Fin N, ∑ j : Fin N, if σ i ≠ j then 1 / ‖x (σ i) - x j‖ else 0) by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp σ (fun j => if σ i ≠ j then 1 / ‖x (σ i) - x j‖ else 0)]
  exact Equiv.sum_comp σ (fun i => ∑ j, if i ≠ j then 1 / ‖x i - x j‖ else 0)

lemma card_small_fin_le (N M : ℕ) : (Finset.univ.filter (fun i : Fin N => i.val < M)).card ≤ M := by
  classical
  have hsubset : (Finset.univ.filter (fun i : Fin N => i.val < M)).image Fin.val ⊆
      Finset.range M := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  have hh := Finset.card_le_card hsubset
  rwa [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_range] at hh

lemma sorted_pairPotential_lower {N : ℕ} (x : Configuration N)
    (hs : Monotone (fun i => ‖x i‖)) (h0 : ∀ i, x i ≠ 0)
    (hi : Function.Injective x) :
    (∑ i : Fin N, (i.val : ℝ) / (2 * ‖x i‖)) ≤ pairPotential x := by
  classical
  unfold pairPotential
  apply Finset.sum_le_sum
  intro i _
  have hr : 0 < ‖x i‖ := norm_pos_iff.mpr (h0 i)
  calc
    _ = ∑ j : Fin N, if j < i then 1 / (2 * ‖x i‖) else 0 := by
      rw [← Finset.sum_filter]
      have he : Finset.univ.filter (fun j : Fin N => j < i) = Finset.Iio i := by
        ext j; simp
      rw [he, Finset.sum_const, Fin.card_Iio, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j < i
      · simp only [hj, ite_true]
        have hn : 0 < ‖x i - x j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hi.ne hj.ne'))
        apply one_div_le_one_div_of_le hn
        have ht := norm_sub_le (x i) (x j)
        linarith [hs hj.le]
      · simp only [hj, ite_false, le_refl]

lemma sorted_potential_stability {N M : ℕ} {Z : ℝ} (_hZ : 0 ≤ Z) (hM : 2 * Z ≤ M)
    (x : Configuration N) (hs : Monotone (fun i => ‖x i‖))
    (h0 : ∀ i, x i ≠ 0) (hi : Function.Injective x) :
    -(1 / 8 : ℝ) * (∑ i, 1 / ‖x i‖ ^ 2) - 2 * Z ^ 2 * M ≤
      -Z * (∑ i, 1 / ‖x i‖) + pairPotential x := by
  classical
  have hp := sorted_pairPotential_lower x hs h0 hi
  have hc := card_small_fin_le N M
  have ht (i : Fin N) : Z * (1 / ‖x i‖) - (i.val : ℝ) / (2 * ‖x i‖) ≤
      (1 / 8 : ℝ) * (1 / ‖x i‖ ^ 2) + (if i.val < M then 2 * Z ^ 2 else 0) := by
    have hr : 0 ≤ 1 / ‖x i‖ := by positivity
    have he : (i.val : ℝ) / (2 * ‖x i‖) = (i.val : ℝ) / 2 * (1 / ‖x i‖) := by ring
    rw [he]
    by_cases hm : i.val < M
    · rw [ite_eq_left hm]
      have hq := sq_nonneg (1 / ‖x i‖ - 4 * Z)
      have hval : 0 ≤ (i.val : ℝ) / 2 * (1 / ‖x i‖) := by positivity
      have heq : (1 / ‖x i‖) ^ 2 = 1 / ‖x i‖ ^ 2 := by ring
      nlinarith [heq]
    · rw [ite_eq_right hm]
      have hge : (M : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast Nat.le_of_not_gt hm
      have hh : 0 ≤ ((i.val : ℝ) / 2 - Z) * (1 / ‖x i‖) :=
        mul_nonneg (by linarith) hr
      have hsq : 0 ≤ 1 / ‖x i‖ ^ 2 := by positivity
      nlinarith
  have ht' := Finset.sum_le_sum (s := Finset.univ) fun i _ => ht i
  have he : (∑ i : Fin N, if i.val < M then 2 * Z ^ 2 else 0) =
      (Finset.univ.filter (fun i : Fin N => i.val < M)).card * (2 * Z ^ 2) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, he] at ht'
  have hc' : ((Finset.univ.filter (fun i : Fin N => i.val < M)).card : ℝ) ≤ M := by
    exact_mod_cast hc
  have hc'' := mul_le_mul_of_nonneg_right hc' (by positivity : 0 ≤ 2 * Z ^ 2)
  linarith

lemma potential_stability {N M : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) (hM : 2 * Z ≤ M)
    (x : Configuration N) (h0 : ∀ i, x i ≠ 0) (hi : Function.Injective x) :
    -(1 / 8 : ℝ) * (∑ i, 1 / ‖x i‖ ^ 2) - 2 * Z ^ 2 * M ≤
      -Z * (∑ i, 1 / ‖x i‖) + pairPotential x := by
  let σ := Tuple.sort (fun i => ‖x i‖)
  have hs : Monotone (fun i => ‖(x ∘ σ) i‖) := Tuple.monotone_sort (fun i => ‖x i‖)
  have hh := sorted_potential_stability hZ hM (x ∘ σ) hs (fun i => h0 (σ i))
    (hi.comp σ.injective)
  rw [pairPotential_perm] at hh
  change -(1 / 8 : ℝ) * (∑ i, 1 / ‖x (σ i)‖ ^ 2) - 2 * Z ^ 2 * M ≤
    -Z * (∑ i, 1 / ‖x (σ i)‖) + pairPotential x at hh
  rw [Equiv.sum_comp σ (fun i => 1 / ‖x i‖ ^ 2),
    Equiv.sum_comp σ (fun i => 1 / ‖x i‖)] at hh
  exact hh

end CoulombAtom

end

end OAI
