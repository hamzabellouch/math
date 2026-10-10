import Mathlib
import OAI.Combinatorics.IndependentSets.Fourier.Fourier

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators
open scoped Classical

lemma degree_eq_sum {n : ℕ} (s : Cube n) :
    (degree s : ℝ) = ∑ i : Fin n, if bit s i then (1:ℝ) else 0 := by
  induction n with
  | zero => simp [degree]
  | succ n ih =>
    obtain ⟨b,s⟩ := s
    rw [Fin.sum_univ_succ]
    cases b <;> simp only [degree, bit, Bool.false_eq_true, ↓reduceIte,
      Fin.cases_zero, Fin.cases_succ, Nat.cast_add, Nat.cast_one,
      zero_add, ih] <;> rfl

def Supported {n : ℕ} (S : Finset (Fin n)) (s : Cube n) : Prop :=
  ∀ i, bit s i = true → i ∈ S

noncomputable def walsh : {n : ℕ} → Cube n → Cube n → ℝ
  | 0, _, _ => 1
  | _+1, (b,s), (c,x) => (if b && c then -1 else 1) * walsh s x

lemma synth_eq_sum {n : ℕ} (a : Cube n → ℝ) (x : Cube n) :
    synth a x = ∑ s, a s * walsh s x := by
  induction n with
  | zero => simp [synth, walsh]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    rw [sum_succ]
    simp only [synth, walsh, Bool.false_and, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte, one_mul, ih]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    ring

lemma walsh_depends {n : ℕ} (s x y : Cube n)
    (h : ∀ i, bit s i = true → bit x i = bit y i) : walsh s x = walsh s y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b,s⟩ := s
    obtain ⟨c,x⟩ := x
    obtain ⟨d,y⟩ := y
    have ht : walsh s x = walsh s y := ih s x y (fun i hi => h i.succ hi)
    have hh : b = true → c = d := fun hb => h 0 hb
    cases b
    · simp [walsh, ht]
    · have he := hh rfl
      subst d
      simp [walsh, ht]

noncomputable def truncate {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ) : Cube n → ℝ :=
  synth (fun s => if Supported S s then fourier f s else 0)

lemma truncate_depends {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ) (x y : Cube n)
    (h : ∀ i ∈ S, bit x i = bit y i) : truncate S f x = truncate S f y := by
  rw [truncate, synth_eq_sum, synth_eq_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Supported S s
  · simp only [ite_eq_left hs]
    rw [walsh_depends s x y (fun i hi => h i (hs i hi))]
  · simp only [ite_eq_right hs, zero_mul]

lemma truncate_error {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ) :
    mean (fun x => (f x - truncate S f x)^2) =
      ∑ s, if Supported S s then 0 else (fourier f s)^2 := by
  rw [← fourier_parseval, fourier_sub]
  simp only [truncate, fourier_synth]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

noncomputable def influence {n : ℕ} (f : Cube n → ℝ) (i : Fin n) : ℝ :=
  mean (fun x => |diff i f x|)

lemma influence_nonneg {n : ℕ} (f : Cube n → ℝ) (i : Fin n) : 0 ≤ influence f i :=
  mean_nonneg (fun _ => abs_nonneg _)

lemma diff_bounded {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1) (i : Fin n) :
    ∀ x, |diff i f x| ≤ 1 := by
  intro x
  dsimp [diff]
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  have h := abs_sub (f x) (f (flip i x))
  linarith [hf x, hf (flip i x)]

lemma diff_square_le_influence {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (i : Fin n) : mean (fun x => diff i f x^2) ≤ influence f i := by
  apply mean_mono
  intro x
  have h := diff_bounded f hf i x
  nlinarith [abs_nonneg (diff i f x), sq_abs (diff i f x)]

lemma weighted_fourier_energy {n : ℕ} (f : Cube n → ℝ) :
    (∑ s, (degree s : ℝ) * (fourier f s)^2) =
      ∑ i : Fin n, mean (fun x => diff i f x^2) := by
  simp_rw [degree_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← fourier_parseval, fourier_diff]
  apply Finset.sum_congr rfl
  intro s _
  cases h : bit s i <;> simp [h]

lemma noise_small_influence {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (i : Fin n) {θ : ℝ} (hθ : 0 ≤ θ) (hi : influence f i ≤ θ^2) :
    mean (fun x => noise (1/2) (diff i f) x^2) ≤ θ * influence f i := by
  have h := noise_small_l1 (diff i f) (diff_bounded f hf i)
  have hI := influence_nonneg f i
  have hN : 0 ≤ mean (fun x => noise (1/2) (diff i f) x^2) := mean_nonneg (fun _ => sq_nonneg _)
  change _ ≤ influence f i ^ 3 at h
  have hm := mul_le_mul_of_nonneg_right hi (sq_nonneg (influence f i))
  nlinarith [mul_nonneg hθ hI]

lemma noise_weight_cancel (d : ℕ) : (4:ℝ)^d * ((1/2:ℝ)^d)^2 = 1 := by
  calc
    _ = ((4:ℝ) * (1/2:ℝ)^2)^d := by rw [mul_pow, pow_right_comm]
    _ = 1 := by norm_num

lemma low_degree_coefficient {n : ℕ} (g : Cube n → ℝ) (s : Cube n) {k : ℕ}
    (hk : degree s ≤ k) :
    (fourier g s)^2 ≤ (4:ℝ)^k * (fourier (noise (1/2) g) s)^2 := by
  rw [fourier_noise]
  have hp : (4:ℝ)^(degree s) ≤ (4:ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
  have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg ((1/2:ℝ)^(degree s)))
  rw [noise_weight_cancel] at hm
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg (fourier g s))
  nlinarith

end LargeIndependentSets.BooleanJunta

end OAI
