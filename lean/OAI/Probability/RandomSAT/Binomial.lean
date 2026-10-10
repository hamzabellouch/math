import OAI.Probability.RandomSAT.ClauseProcess

namespace OAI

/-!
Finite Bernoulli-count expectations and integrated telescoping estimates.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def binomialMean (p : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, f => f 0
  | m + 1, f => (1 - p) * binomialMean p m f +
      p * binomialMean p m (fun d => f (d + 1))

theorem binomialMean_congr {p : ℝ} {m : ℕ} {f g : ℕ → ℝ}
    (h : ∀ d ≤ m, f d = g d) : binomialMean p m f = binomialMean p m g := by
  induction m generalizing f g with
  | zero => exact h 0 (by omega)
  | succ m ih =>
    simp only [binomialMean]
    rw [ih (fun d hd => h d (by omega)), ih (fun d hd => h (d + 1) (by omega))]

theorem binomialMean_const (p c : ℝ) (m : ℕ) : binomialMean p m (fun _ => c) = c := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [binomialMean, ih]; ring

theorem binomialMean_add (p : ℝ) (m : ℕ) (f g : ℕ → ℝ) :
    binomialMean p m (fun d => f d + g d) = binomialMean p m f + binomialMean p m g := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih => simp only [binomialMean, ih]; ring

theorem binomialMean_sub (p : ℝ) (m : ℕ) (f g : ℕ → ℝ) :
    binomialMean p m (fun d => f d - g d) = binomialMean p m f - binomialMean p m g := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih => simp only [binomialMean, ih]; ring

theorem binomialMean_mul_const (p c : ℝ) (m : ℕ) (f : ℕ → ℝ) :
    binomialMean p m (fun d => f d * c) = binomialMean p m f * c := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => simp only [binomialMean, ih]; ring

theorem binomialMean_const_mul (p c : ℝ) (m : ℕ) (f : ℕ → ℝ) :
    binomialMean p m (fun d => c * f d) = c * binomialMean p m f := by
  simpa only [mul_comm] using binomialMean_mul_const p c m f

theorem binomialMean_sum {ι : Type*} (p : ℝ) (m : ℕ) (s : Finset ι) (f : ι → ℕ → ℝ) :
    binomialMean p m (fun d => ∑ i ∈ s, f i d) = ∑ i ∈ s, binomialMean p m (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [binomialMean_const]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, binomialMean_add, ih]

theorem binomialMean_mono {p : ℝ} {m : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : ℕ → ℝ} (h : ∀ d ≤ m, f d ≤ g d) : binomialMean p m f ≤ binomialMean p m g := by
  induction m generalizing f g with
  | zero => exact h 0 (by omega)
  | succ m ih =>
    exact add_le_add
      (mul_le_mul_of_nonneg_left (ih (fun d hd => h d (by omega))) (sub_nonneg.mpr hp1))
      (mul_le_mul_of_nonneg_left (ih (fun d hd => h (d + 1) (by omega))) hp0)

theorem binomialMean_nonneg {p : ℝ} {m : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f : ℕ → ℝ} (h : ∀ d ≤ m, 0 ≤ f d) : 0 ≤ binomialMean p m f := by
  simpa only [binomialMean_const] using binomialMean_mono hp0 hp1 h

theorem binomialMean_id (p : ℝ) (m : ℕ) :
    binomialMean p m (fun d => (d : ℝ)) = (m : ℝ) * p := by
  induction m with
  | zero => simp [binomialMean]
  | succ m ih =>
    simp only [binomialMean, Nat.cast_add, Nat.cast_one, binomialMean_add,
      binomialMean_const, ih]
    ring

theorem binomialMean_monotone_trials {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f : ℕ → ℝ} (hf : Monotone f) : Monotone (fun m => binomialMean p m f) := by
  apply monotone_nat_of_le_succ
  intro m
  have h := binomialMean_mono (m := m) hp0 hp1 (f := f) (g := fun d => f (d + 1))
    (fun d _ => hf (by omega))
  change _ ≤ (1 - p) * _ + p * _
  nlinarith

theorem uniformMean_binomialMean {α : Type*} [Fintype α]
    (p : ℝ) (m : ℕ) (f : ℕ → α → ℝ) :
    uniformMean (fun a => binomialMean p m (fun d => f d a)) =
      binomialMean p m (fun d => uniformMean (f d)) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    simp only [binomialMean, uniformMean_add, uniformMean_const_mul, ih]

theorem sum_shift_difference_le (P : ℕ → ℝ) (hP0 : ∀ j, 0 ≤ P j)
    (hP1 : ∀ j, P j ≤ 1) (l b : ℕ) :
    ∑ j ∈ Finset.range l, (P j - P (j + b)) ≤ (b : ℝ) := by
  have h1 := Finset.sum_range_add P l b
  have h2 := Finset.sum_range_add P b l
  have hid : (∑ j ∈ Finset.range l, (P j - P (j + b))) =
      ∑ j ∈ Finset.range b, (P j - P (j + l)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have hc : l + b = b + l := Nat.add_comm _ _
    simp only [Nat.add_comm l] at h1
    simp only [Nat.add_comm b] at h2
    rw [hc] at h2
    linarith
  rw [hid]
  calc
    _ ≤ ∑ _j ∈ Finset.range b, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      linarith [hP0 (j + l), hP1 j]
    _ = b := by simp

theorem sum_two_shift_difference_le (P : ℕ → ℝ) (hP0 : ∀ j, 0 ≤ P j)
    (hP1 : ∀ j, P j ≤ 1) (l a b : ℕ) :
    ∑ j ∈ Finset.range l, (P (j - a) - P (j + b)) ≤ (a : ℝ) + b := by
  have h1 := sum_shift_difference_le (fun j => P (j - a))
    (fun j => hP0 _) (fun j => hP1 _) l a
  simp only [Nat.add_sub_cancel] at h1
  have h2 := sum_shift_difference_le P hP0 hP1 l b
  have he : (∑ j ∈ Finset.range l, (P (j - a) - P (j + b))) =
      (∑ j ∈ Finset.range l, (P (j - a) - P j)) +
      ∑ j ∈ Finset.range l, (P j - P (j + b)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  linarith

def replacementDifference (P : ℕ → ℝ) (g j d : ℕ) : ℝ :=
  P (j - d) - P (j + (g - 1) * d)

theorem replacementDifference_mono {P : ℕ → ℝ} (hP : Antitone P) (g j : ℕ) :
    Monotone (replacementDifference P g j) := by
  intro d e hde
  apply sub_le_sub
  · exact hP (Nat.sub_le_sub_left hde j)
  · exact hP (Nat.add_le_add_left (Nat.mul_le_mul_left _ hde) j)

theorem replacementDifference_sum_le {P : ℕ → ℝ}
    (hP0 : ∀ j, 0 ≤ P j) (hP1 : ∀ j, P j ≤ 1) {g : ℕ} (hg : 1 ≤ g) (l d : ℕ) :
    ∑ j ∈ Finset.range l, replacementDifference P g j d ≤ (g : ℝ) * d := by
  have h := sum_two_shift_difference_le P hP0 hP1 l d ((g - 1) * d)
  have he : (d : ℝ) + ((g - 1) * d : ℕ) = (g : ℝ) * d := by
    rw [Nat.cast_mul, Nat.cast_sub hg]
    push_cast
    ring
  simpa only [replacementDifference, he] using h

theorem binomial_replacement_sum_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P : ℕ → ℝ} (hP : Antitone P) (hP0 : ∀ j, 0 ≤ P j) (hP1 : ∀ j, P j ≤ 1)
    {g : ℕ} (hg : 1 ≤ g) (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), binomialMean p j (replacementDifference P g j) ≤
      (g : ℝ) * (M : ℝ) * p := by
  calc
    _ ≤ ∑ j ∈ Finset.range (M + 1), binomialMean p M (replacementDifference P g j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjM : j ≤ M := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      exact binomialMean_monotone_trials hp0 hp1 (replacementDifference_mono hP g j) hjM
    _ = binomialMean p M (fun d => ∑ j ∈ Finset.range (M + 1),
        replacementDifference P g j d) := (binomialMean_sum _ _ _ _).symm
    _ ≤ binomialMean p M (fun d => (g : ℝ) * d) :=
      binomialMean_mono hp0 hp1 (fun d _ => replacementDifference_sum_le hP0 hP1 hg _ d)
    _ = _ := by rw [binomialMean_const_mul, binomialMean_id]; ring

end


end FixedClauseThreshold

end OAI
