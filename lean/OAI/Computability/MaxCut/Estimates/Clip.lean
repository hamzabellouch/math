import Mathlib
import OAI.Computability.MaxCut.Gadgets.Polynomial
import OAI.Computability.MaxCut.Encoding.BitCube

namespace OAI

noncomputable section
namespace OptimalMaxCut.MISProof
open scoped BigOperators
open Finset Set MaxCutGames.Foundations.Hastad Analytic BooleanFourthMoment GaussianBellman

 theorem degree_cons {n : ℕ} (a : Bool) (s : Cube (Fin n)) :
    degree (Fin.cons a s) = degree s + if a then 1 else 0 := by
  simp only [degree, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  cases a <;> simp [Nat.add_comm]

 theorem corrAverage_sum {ι : Type*} (S : Finset ι) (t : ℝ) (n : ℕ)
    (F : ι → BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => ∑ i ∈ S, F i x y) = ∑ i ∈ S, corrAverage t n (F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using corrAverage_fst t n (fun _ => 0)
  | @insert a S ha ih => simp only [Finset.sum_insert ha, corrAverage_add, ih]

 theorem corrAverage_walsh (t : ℝ) (n : ℕ) (s r : Cube (Fin n)) :
    corrAverage t n (fun x y => walsh s x * walsh r y) =
      if s = r then t ^ degree s else 0 := by
  induction n with
  | zero => simp [corrAverage, walsh, degree, Subsingleton.elim s r]
  | succ n ih =>
    obtain ⟨⟨a, s⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective s
    obtain ⟨⟨b, r⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective r
    change corrAverage t (n + 1) (fun x y => walsh (Fin.cons a s) x * walsh (Fin.cons b r) y) =
      if (Fin.cons a s : Cube (Fin (n + 1))) = Fin.cons b r then t ^ degree (Fin.cons a s) else 0
    have hp (x y : Cube (Fin n)) :
        (∑ e : Bool, ∑ f : Bool, bitPairWeight t e f *
          (walsh (Fin.cons a s) (Fin.cons e x) * walsh (Fin.cons b r) (Fin.cons f y))) =
        (if a = b then (if a then t else 1) else 0) * (walsh s x * walsh r y) := by
      cases a <;> cases b <;>
        simp only [Fintype.sum_bool, bitPairWeight, sign, walsh_cons, bitSign,
          Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;> ring
    simp only [corrAverage, hp, corrAverage_const_mul, ih, Fin.cons_inj, degree_cons]
    cases a <;> cases b <;> by_cases h : s = r <;> simp [h, pow_succ, mul_comm]

 theorem corrAverage_polynomial (t : ℝ) (n : ℕ) (c d : Cube (Fin n) → ℝ) :
    corrAverage t n (fun x y => polynomial c x * polynomial d y) =
      ∑ s, t ^ degree s * c s * d s := by
  have hp (x y : Cube (Fin n)) : polynomial c x * polynomial d y =
      ∑ s, ∑ r, (c s * d r) * (walsh s x * walsh r y) := by
    simp only [polynomial]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp only [hp, corrAverage_sum, corrAverage_const_mul, corrAverage_walsh]
  apply Finset.sum_congr rfl
  intro s _
  simp [mul_ite]
  ring

 theorem corrAverage_stability (t : ℝ) (n : ℕ) (f : Cube (Fin n) → ℝ) :
    corrAverage t n (fun x y => f x * f y) = stability t f := by
  have hf : polynomial (coefficient f) = f := funext (walsh_inversion f)
  rw [← hf, corrAverage_polynomial]
  simp only [stability, coefficient_polynomial]
  apply Finset.sum_congr rfl
  intro s _
  ring

noncomputable def clip (x : ℝ) : ℝ := max (-1) (min 1 x)

 theorem clip_mem (x : ℝ) : clip x ∈ Icc (-1 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

 theorem clip_eq {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : clip x = x := by
  rw [clip, min_eq_right hx.2, max_eq_right hx.1]

 theorem clip_lipschitz (a b : ℝ) : |clip a - clip b| ≤ |a - b| := by
  have h1 := le_abs_self (a - b)
  have h2 := neg_le_abs (a - b)
  unfold clip
  simp only [max_def, min_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

noncomputable def interiorClip (η x : ℝ) : ℝ := η + (1 - 2 * η) * (clip x + 1) / 2

 theorem interiorClip_mem {η : ℝ} (_hη : 0 ≤ η) (hη' : η ≤ 1 / 2) (x : ℝ) :
    interiorClip η x ∈ Icc η (1 - η) := by
  have hx := clip_mem x
  have hl := mul_nonneg (by linarith : 0 ≤ 1 - 2 * η) (by linarith [hx.1] : 0 ≤ clip x + 1)
  have hu := mul_le_mul_of_nonneg_left (by linarith [hx.2] : clip x + 1 ≤ 2)
    (by linarith : 0 ≤ 1 - 2 * η)
  unfold interiorClip
  constructor <;> linarith

 theorem interiorClip_lipschitz {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2) (a b : ℝ) :
    |interiorClip η a - interiorClip η b| ≤ |a - b| := by
  have hc : 0 ≤ (1 - 2 * η) / 2 := by linarith
  have hc' : (1 - 2 * η) / 2 ≤ 1 := by linarith
  have he : interiorClip η a - interiorClip η b = (1 - 2 * η) / 2 * (clip a - clip b) := by
    unfold interiorClip; ring
  rw [he, abs_mul, abs_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left (clip_lipschitz a b) hc).trans
    (by simpa using mul_le_mul_of_nonneg_right hc' (abs_nonneg (a - b)))

 theorem interiorClip_approx {η b : ℝ} (hη : 0 ≤ η) (hb : b ∈ Icc (-1 : ℝ) 1) (a : ℝ) :
    |interiorClip η a - (b + 1) / 2| ≤ |a - b| + η := by
  have he : interiorClip η a - (b + 1) / 2 = (clip a - b) / 2 + (-η * clip a) := by
    unfold interiorClip; ring
  have hc : |clip a| ≤ 1 := abs_le.mpr (clip_mem a)
  have hab : |clip a - b| ≤ |a - b| := by
    simpa only [clip_eq hb] using clip_lipschitz a b
  rw [he]
  calc
    _ ≤ |(clip a - b) / 2| + |-η * clip a| := abs_add_le _ _
    _ = |clip a - b| / 2 + η * |clip a| := by
      rw [abs_div, abs_mul, abs_neg, abs_of_nonneg hη]; norm_num
    _ ≤ |a - b| / 2 + η * 1 := add_le_add (by linarith) (mul_le_mul_of_nonneg_left hc hη)
    _ ≤ _ := by linarith [abs_nonneg (a - b)]

 theorem mean_abs_diff_le {n : ℕ} (f g : BitCube n → ℝ) :
    |(𝔼 x, f x) - (𝔼 x, g x)| ≤ 𝔼 x, |f x - g x| := by
  rw [← Finset.expect_sub_distrib]
  apply abs_le.mpr
  constructor
  · rw [← Finset.expect_neg_distrib]
    exact Finset.expect_le_expect (fun x _ => neg_le_of_abs_le (le_refl |f x - g x|))
  · exact Finset.expect_le_expect (fun x _ => le_abs_self _)

 theorem correlation_diff_le {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {n : ℕ}
    (f g : BitCube n → ℝ) (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hg : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    corrAverage t n (fun x y => f x * f y) ≤
      corrAverage t n (fun x y => g x * g y) + 2 * (𝔼 x, |f x - g x|) := by
  have hp (x y : BitCube n) : f x * f y ≤ g x * g y + |f x - g x| + |f y - g y| := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self (f x - g x)) (hf y).1
    have h2 := mul_le_mul_of_nonneg_left (hf y).2 (abs_nonneg (f x - g x))
    have h3 := mul_le_mul_of_nonneg_left (le_abs_self (f y - g y)) (hg x).1
    have h4 := mul_le_mul_of_nonneg_right (hg x).2 (abs_nonneg (f y - g y))
    nlinarith
  have hh := corrAverage_mono ht n hp
  rw [corrAverage_add, corrAverage_add, corrAverage_fst, corrAverage_snd] at hh
  linarith

 theorem centered_half_correlation (t : ℝ) (n : ℕ) (h : BitCube n → ℝ) (hm : (𝔼 x, h x) = 0) :
    4 * corrAverage t n (fun x y => ((h x + 1) / 2) * ((h y + 1) / 2)) - 1 = stability t h := by
  have hp (x y : BitCube n) : ((h x + 1) / 2) * ((h y + 1) / 2) =
      (h x * h y + h x + h y + 1) * (1 / 4) := by ring
  simp_rw [hp]
  rw [corrAverage_mul_const, corrAverage_add, corrAverage_add, corrAverage_add,
    corrAverage_fst, corrAverage_fst, corrAverage_snd, corrAverage_stability, hm,
    Fintype.expect_const]
  ring

noncomputable def smoothedTruncCoeff {n : ℕ} (K : ℕ) (u : ℝ) (h : BitCube n → ℝ)
    (s : BitCube n) : ℝ := if degree s ≤ K then u ^ degree s * coefficient h s else 0

 theorem smoothedTrunc_high {n K : ℕ} (u : ℝ) (h : BitCube n → ℝ)
    (s : BitCube n) (hs : K < degree s) : smoothedTruncCoeff K u h s = 0 := by
  simp [smoothedTruncCoeff, not_le.mpr hs]

 theorem smoothedTrunc_sq_le {n K : ℕ} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (h : BitCube n → ℝ) (s : BitCube n) : smoothedTruncCoeff K u h s ^ 2 ≤ coefficient h s ^ 2 := by
  unfold smoothedTruncCoeff
  split_ifs
  · rw [mul_pow]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (pow_nonneg hu.1 _) (pow_le_one₀ hu.1 hu.2))
      (sq_nonneg _)).trans_eq (one_mul _)
  · simpa only [zero_pow (by omega : 2 ≠ 0)] using sq_nonneg (coefficient h s)

 theorem smoothedTrunc_second_le {n K : ℕ} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (h : BitCube n → ℝ) (hh : ∀ x, h x ∈ Icc (-1 : ℝ) 1) :
    (𝔼 x, polynomial (smoothedTruncCoeff K u h) x ^ 2) ≤ 1 := by
  rw [polynomial_second_moment]
  exact (Finset.sum_le_sum (fun s _ => smoothedTrunc_sq_le hu h s)).trans (spectral_energy_le_one h hh)

 theorem smoothedTrunc_diff_second {n K : ℕ} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (h : BitCube n → ℝ) (i : Fin n) :
    (𝔼 x, discreteDiff (polynomial (smoothedTruncCoeff K u h)) i x ^ 2) ≤ cutoffInfluence K i h := by
  rw [polynomial_diff, polynomial_second_moment]
  unfold cutoffInfluence
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro s _
  by_cases hi : s i = true
  · simp only [hi, ↓reduceIte, true_and]
    by_cases hs : degree s ≤ K
    · rw [ite_eq_left hs]; exact smoothedTrunc_sq_le hu h s
    · simp [smoothedTruncCoeff, hs]
  · simp [hi]

 theorem coefficient_sub {n : ℕ} (f g : BitCube n → ℝ) (s : BitCube n) :
    coefficient (fun x => f x - g x) s = coefficient f s - coefficient g s := by
  simp only [coefficient, sub_mul, Finset.expect_sub_distrib]

 theorem smoothedTrunc_tail_second {n K : ℕ} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (h : BitCube n → ℝ) (hh : ∀ x, h x ∈ Icc (-1 : ℝ) 1) :
    (𝔼 x, (polynomial (smoothedTruncCoeff K u h) x - noise u h x) ^ 2) ≤ u ^ (2 * (K + 1)) := by
  rw [← walsh_parseval]
  simp only [coefficient_sub, coefficient_polynomial, coefficient_noise]
  calc
    _ ≤ ∑ s, u ^ (2 * (K + 1)) * coefficient h s ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : degree s ≤ K
      · simp only [smoothedTruncCoeff, ite_eq_left hs, sub_self, zero_pow (by omega : 2 ≠ 0)]
        exact mul_nonneg (pow_nonneg hu.1 _) (sq_nonneg _)
      · have hd : 2 * (K + 1) ≤ degree s * 2 := by omega
        have hp := pow_le_pow_of_le_one hu.1 hu.2 hd
        simp only [smoothedTruncCoeff, ite_eq_right hs, zero_sub, neg_sq, mul_pow, ← pow_mul]
        exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)
    _ = u ^ (2 * (K + 1)) * ∑ s, coefficient h s ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ u ^ (2 * (K + 1)) * 1 := mul_le_mul_of_nonneg_left (spectral_energy_le_one h hh) (pow_nonneg hu.1 _)
    _ = _ := mul_one _

 theorem mean_abs_le_of_second {n : ℕ} (f : BitCube n → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : (𝔼 x, f x ^ 2) ≤ ε ^ 2) : (𝔼 x, |f x|) ≤ ε := by
  have hCS := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (fun x => |f x|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sq_abs, Fintype.expect_const] at hCS
  exact (sq_le_sq₀ (by positivity) hε).mp (hCS.trans hf)

 theorem smoothedTrunc_tail_first {n K : ℕ} {u ε : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hε : 0 ≤ ε) (htail : u ^ (2 * (K + 1)) ≤ ε ^ 2)
    (h : BitCube n → ℝ) (hh : ∀ x, h x ∈ Icc (-1 : ℝ) 1) :
    (𝔼 x, |polynomial (smoothedTruncCoeff K u h) x - noise u h x|) ≤ ε :=
  mean_abs_le_of_second _ hε ((smoothedTrunc_tail_second hu h hh).trans htail)

 theorem clipped_polynomial_bellman {t η : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hη : 0 < η) (hη' : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n K : ℕ) (c : BitCube n → ℝ) (τ : ℝ), 0 ≤ τ →
      (∀ s, K < degree s → c s = 0) →
      (𝔼 x, polynomial c x ^ 2) ≤ 1 →
      (∀ i, (𝔼 x, discreteDiff (polynomial c) i x ^ 2) ≤ τ ^ 2) →
      corrAverage t n (fun x y => interiorClip η (polynomial c x) * interiorClip η (polynomial c y)) ≤
        kernel t (𝔼 x, interiorClip η (polynomial c x)) (𝔼 x, interiorClip η (polynomial c x)) +
          2 * C * (3 ^ K * τ * K) := by
  obtain ⟨C, hC0, hC⟩ := kernel_one_bit ht hη hη'
  refine ⟨C, hC0, ?_⟩
  intro n K c τ hτ hc hsecond hsmall
  let F : BitCube n → ℝ := fun x => interiorClip η (polynomial c x)
  have hcost : cubicCost n F ≤ 3 ^ K * τ * K := by
    calc
      _ ≤ ∑ i, 𝔼 x, |gradient F i x| ^ 3 := cubicCost_le_gradients n F
      _ ≤ ∑ i, 𝔼 x, |discreteDiff (polynomial c) i x| ^ 3 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.expect_le_expect
        intro x _
        exact pow_le_pow_left₀ (abs_nonneg _)
          (gradient_lipschitz (interiorClip η) (interiorClip_lipschitz hη.le hη') (polynomial c) i x) 3
      _ ≤ 3 ^ K * τ * K * (𝔼 x, polynomial c x ^ 2) := total_diff_third_truncated c hc hτ hsmall
      _ ≤ 3 ^ K * τ * K * 1 := mul_le_mul_of_nonneg_left hsecond (by positivity)
      _ = _ := mul_one _
  have hF (x : BitCube n) : F x ∈ Icc η (1 - η) := interiorClip_mem hη.le hη' _
  have htt : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2.le⟩
  have hb := finite_bellman_tensorization htt (kernel t) hC n F F hF hF
  have hm := corrAverage_mono htt n (fun x y => kernel_ge_product ht (F x) (F y))
  have he := mul_le_mul_of_nonneg_left hcost hC0
  change corrAverage t n (fun x y => F x * F y) ≤
    kernel t (𝔼 x, F x) (𝔼 x, F x) + 2 * C * (3 ^ K * τ * K)
  linarith

 theorem mean_mem_Icc {n : ℕ} {l u : ℝ} (f : BitCube n → ℝ) (hf : ∀ x, f x ∈ Icc l u) :
    (𝔼 x, f x) ∈ Icc l u :=
  ⟨Finset.le_expect Finset.univ_nonempty (fun x _ => (hf x).1),
    Finset.expect_le Finset.univ_nonempty (fun x _ => (hf x).2)⟩

 theorem smoothed_stability_bellman {t η u τ C : ℝ} {n K : ℕ}
    (ht : t ∈ Ico (0 : ℝ) 1) (hη : 0 < η) (hη' : η ≤ 1 / 2)
    (hu : u ∈ Icc (0 : ℝ) 1)
    (h : BitCube n → ℝ) (hh : ∀ x, h x ∈ Icc (-1 : ℝ) 1) (hm : (𝔼 x, h x) = 0)
    (htail : u ^ (2 * (K + 1)) ≤ η ^ 2)
    (hb : corrAverage t n (fun x y =>
        interiorClip η (polynomial (smoothedTruncCoeff K u h) x) *
          interiorClip η (polynomial (smoothedTruncCoeff K u h) y)) ≤
      kernel t (𝔼 x, interiorClip η (polynomial (smoothedTruncCoeff K u h) x))
        (𝔼 x, interiorClip η (polynomial (smoothedTruncCoeff K u h) x)) + 2 * C * (3 ^ K * τ * K)) :
    stability t (noise u h) ≤ 2 / Real.pi * Real.arcsin t + 32 * η + 8 * C * (3 ^ K * τ * K) := by
  let P := polynomial (smoothedTruncCoeff K u h)
  let F : BitCube n → ℝ := fun x => interiorClip η (P x)
  let G : BitCube n → ℝ := fun x => (noise u h x + 1) / 2
  have hnoise := noise_bounded u hu.1 hu.2 h hh
  have hmean : (𝔼 x, G x) = 1 / 2 := by
    change (𝔼 x, ((noise u h x + 1) / 2)) = 1 / 2
    rw [← Finset.expect_div, Finset.expect_add_distrib, noise_mean, hm, Fintype.expect_const]
    ring
  have hF (x : BitCube n) : F x ∈ Icc η (1 - η) := interiorClip_mem hη.le hη' _
  have hF01 (x : BitCube n) : F x ∈ Icc (0 : ℝ) 1 := by
    have hhx := hF x
    constructor <;> linarith [hhx.1, hhx.2]
  have hG01 (x : BitCube n) : G x ∈ Icc (0 : ℝ) 1 := by
    dsimp [G]
    constructor <;> linarith [(hnoise x).1, (hnoise x).2]
  have hdiff : (𝔼 x, |F x - G x|) ≤ 2 * η := by
    calc
      _ ≤ 𝔼 x, (|P x - noise u h x| + η) :=
        Finset.expect_le_expect (fun x _ => interiorClip_approx hη.le (hnoise x) (P x))
      _ = (𝔼 x, |P x - noise u h x|) + η := by rw [Finset.expect_add_distrib, Fintype.expect_const]
      _ ≤ 2 * η := by linarith [smoothedTrunc_tail_first hu hη.le htail h hh]
  have hmeanF : (𝔼 x, F x) ∈ Ioo (0 : ℝ) 1 := by
    have hhF := mean_mem_Icc F hF
    constructor <;> linarith [hhF.1, hhF.2]
  have hmeanDiff : |(𝔼 x, F x) - (1 / 2 : ℝ)| ≤ 2 * η := by
    have hbnd := (mean_abs_diff_le F G).trans hdiff
    rwa [hmean] at hbnd
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hk := kernel_lipschitz ht hhalf hmeanF hhalf hmeanF
  have hk' := (abs_le.mp hk).2
  rw [kernel_half ht] at hk'
  have hcorr := correlation_diff_le ⟨by linarith [ht.1], ht.2.le⟩ G F hG01 hF01
  have heq : (𝔼 x, |G x - F x|) = 𝔼 x, |F x - G x| := by simp only [abs_sub_comm]
  rw [heq] at hcorr
  have hnmean : (𝔼 x, noise u h x) = 0 := (noise_mean u h).trans hm
  have hid := centered_half_correlation t n (noise u h) hnmean
  change 4 * corrAverage t n (fun x y => G x * G y) - 1 = stability t (noise u h) at hid
  change corrAverage t n (fun x y => F x * F y) ≤
    kernel t (𝔼 x, F x) (𝔼 x, F x) + 2 * C * (3 ^ K * τ * K) at hb
  have halg : 4 * (Real.arcsin t / (2 * Real.pi)) = 2 / Real.pi * Real.arcsin t := by ring
  linarith

 theorem majority_is_stablest : MajorityIsStablest := by
  intro t ht ht1 ξ hξ
  obtain ⟨u, hu, hu1, huerr⟩ := exists_uniform_noise_error t ξ ht.le ht1 hξ
  let η : ℝ := min (1 / 4) (ξ / 128)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηsmall : η ≤ 1 / 4 := min_le_left _ _
  have hηξ : η ≤ ξ / 128 := min_le_right _ _
  have hηhalf : η ≤ 1 / 2 := by linarith
  obtain ⟨C, hC0, hC⟩ := clipped_polynomial_bellman ⟨ht.le, ht1⟩ hη hηhalf
  obtain ⟨K, hK, htail⟩ := exists_influence_tail_cutoff u (2 * η ^ 2) hu.le hu1 (by positivity)
  have htail' : u ^ (2 * (K + 1)) ≤ η ^ 2 := by linarith
  let D : ℝ := 8 * C * 3 ^ K * K
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let r : ℝ := (ξ / 4) / (D + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrEq : (D + 1) * r = ξ / 4 := by
    dsimp [r]
    field_simp
  have herr : D * r ≤ ξ / 4 := by nlinarith
  refine ⟨K, hK, r ^ 2, sq_pos_of_pos hr, ?_⟩
  intro n h hh hm hi
  have hsmall (i : Fin n) :
      (𝔼 x, discreteDiff (polynomial (smoothedTruncCoeff K u h)) i x ^ 2) ≤ r ^ 2 :=
    (smoothedTrunc_diff_second ⟨hu.le, hu1.le⟩ h i).trans (hi i).le
  have hb := hC n K (smoothedTruncCoeff K u h) r hr.le
    (smoothedTrunc_high u h) (smoothedTrunc_second_le ⟨hu.le, hu1.le⟩ h hh) hsmall
  have hst := smoothed_stability_bellman ⟨ht.le, ht1⟩ hη hηhalf ⟨hu.le, hu1.le⟩ h hh hm htail' hb
  have hsmooth := stability_sub_noise_le t u (ξ / 2) h hh (by positivity) huerr
  have halg : 8 * C * (3 ^ K * r * K) = D * r := by dsimp [D]; ring
  rw [halg] at hst
  linarith

 theorem cutoffInfluence_le_influence {n : ℕ} (K : ℕ) (i : Fin n) (h : BitCube n → ℝ) :
    cutoffInfluence K i h ≤ influence i h := by
  unfold cutoffInfluence influence
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hs.1
  · intro s _ _; exact sq_nonneg _

 theorem untruncated_majority_is_stablest : UntruncatedMajorityIsStablest := by
  intro t ht ht1 ξ hξ
  obtain ⟨K, _, τ, hτ, hbound⟩ := majority_is_stablest t ht ht1 ξ hξ
  refine ⟨τ, hτ, ?_⟩
  intro n h hh hm hi
  exact hbound n h hh hm (fun i => (cutoffInfluence_le_influence K i h).trans_lt (hi i))

end OptimalMaxCut.MISProof

namespace OptimalMaxCut.LongCode

open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad OptimalMaxCut.Analytic
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

/-- Explicit rational finite probability law. The weighted test below is a
finite rational graph construction, not an oracle distribution. -/
structure Law (I : Type*) [Fintype I] where
  weight : I → ℚ
  nonneg : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1

namespace Law
variable {I J : Type*} [Fintype I] [Fintype J]

def avg (p : Law I) (f : I → ℝ) : ℝ := ∑ i, (p.weight i : ℝ) * f i

theorem weight_nonneg (p : Law I) (i : I) : 0 ≤ (p.weight i : ℝ) := by
  exact_mod_cast p.nonneg i

theorem total_real (p : Law I) : ∑ i, (p.weight i : ℝ) = 1 := by
  exact_mod_cast p.total

@[simp] theorem avg_const (p : Law I) (a : ℝ) : p.avg (fun _ => a) = a := by
  simp [avg, ← sum_mul, total_real]

theorem avg_mono (p : Law I) {f g : I → ℝ} (h : ∀ i, f i ≤ g i) : p.avg f ≤ p.avg g :=
  sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (p.weight_nonneg i)

theorem avg_nonneg (p : Law I) {f : I → ℝ} (h : ∀ i, 0 ≤ f i) : 0 ≤ p.avg f := by
  simpa using p.avg_mono h

@[simp] theorem avg_add (p : Law I) (f g : I → ℝ) :
    p.avg (fun i => f i + g i) = p.avg f + p.avg g := by simp [avg, mul_add, sum_add_distrib]

@[simp] theorem avg_sub (p : Law I) (f g : I → ℝ) :
    p.avg (fun i => f i - g i) = p.avg f - p.avg g := by simp [avg, mul_sub, sum_sub_distrib]

@[simp] theorem avg_mul (p : Law I) (f : I → ℝ) (a : ℝ) :
    p.avg (fun i => f i * a) = p.avg f * a := by simp [avg, sum_mul, mul_assoc]

@[simp] theorem avg_smul (p : Law I) (f : I → ℝ) (a : ℝ) :
    p.avg (fun i => a * f i) = a * p.avg f := by simp [avg, mul_left_comm, mul_sum]

@[simp] theorem avg_div (p : Law I) (f : I → ℝ) (a : ℝ) :
    p.avg (fun i => f i / a) = p.avg f / a := by simp [div_eq_mul_inv]

theorem avg_sum (p : Law I) (f : J → I → ℝ) :
    p.avg (fun i => ∑ j, f j i) = ∑ j, p.avg (f j) := by
  simp_rw [avg, mul_sum]
  rw [sum_comm]

theorem avg_avg (p : Law I) (q : Law J) (f : I → J → ℝ) :
    p.avg (fun i => q.avg (f i)) = q.avg (fun j => p.avg (fun i => f i j)) := by
  simp_rw [avg, mul_sum]
  rw [sum_comm]
  simp_rw [mul_left_comm]

theorem avg_sq_le (p : Law I) (f : I → ℝ) : p.avg f ^ 2 ≤ p.avg (fun i => f i ^ 2) := by
  have h := p.avg_nonneg (fun i => sq_nonneg (f i - p.avg f))
  have he : p.avg (fun i => (f i - p.avg f) ^ 2) = p.avg (fun i => f i ^ 2) - p.avg f ^ 2 := by
    simp_rw [sub_sq]
    rw [avg_add, avg_sub, avg_mul, avg_smul, avg_const]
    ring
  rw [he] at h
  linarith

theorem avg_mem (p : Law I) {f : I → ℝ} {a b : ℝ} (h : ∀ i, f i ∈ Set.Icc a b) :
    p.avg f ∈ Set.Icc a b := by
  constructor
  · simpa using p.avg_mono (fun i => (h i).1)
  · simpa using p.avg_mono (fun i => (h i).2)

 theorem avg_expect {n : ℕ} (p : Law I) (f : I → Cube (Fin n) → ℝ) :
    (𝔼 x, p.avg (fun i => f i x)) = p.avg (fun i => 𝔼 x, f i x) := by
  simp_rw [avg, Finset.expect_sum_comm, ← Finset.mul_expect]

 theorem coefficient_avg {n : ℕ} (p : Law I) (f : I → Cube (Fin n) → ℝ)
    (s : Cube (Fin n)) :
    coefficient (fun x => p.avg (fun i => f i x)) s = p.avg (fun i => coefficient (f i) s) := by
  simp_rw [coefficient, avg, sum_mul, mul_assoc, Finset.expect_sum_comm, ← Finset.mul_expect]

 theorem cutoffInfluence_avg {n : ℕ} (p : Law I) (f : I → Cube (Fin n) → ℝ)
    (K : ℕ) (a : Fin n) :
    cutoffInfluence K a (fun x => p.avg (fun i => f i x)) ≤
      p.avg (fun i => cutoffInfluence K a (f i)) := by
  unfold cutoffInfluence
  simp_rw [coefficient_avg]
  calc
    _ ≤ ∑ s ∈ univ.filter (fun s : Cube (Fin n) => s a = true ∧ degree s ≤ K),
        p.avg (fun i => coefficient (f i) s ^ 2) := sum_le_sum fun s _ => p.avg_sq_le _
    _ = _ := by simp_rw [avg, mul_sum]; rw [sum_comm]

end Law

/-- The generative presentation of a finite rational weighted Unique Game:
choose a right question, then an incident edge. All actual games have this
presentation after deleting zero-marginal right questions. -/
structure Game (X Y E : Type*) [Fintype X] [Fintype Y] [Fintype E] (q : ℕ) where
  rightLaw : Law Y
  edgeLaw : Y → Law E
  source : E → X
  permutation : E → Equiv.Perm (Fin q)

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

noncomputable def satisfied (G : Game X Y E q) (lx : X → Fin q) (ly : Y → Fin q) : ℝ :=
  G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
    if G.permutation e (lx (G.source e)) = ly y then 1 else 0))

/-- A semantic bound on this *input* game, not a hypothesis asserting NP-hardness
or an assumed Max-Cut reduction. -/
def Sound (G : Game X Y E q) (δ : ℝ) : Prop := ∀ lx ly, G.satisfied lx ly ≤ δ

end Game

noncomputable def antipode {n : ℕ} (x : Cube (Fin n)) : Cube (Fin n) := fun i => !(x i)

 theorem antipode_involutive {n : ℕ} : Function.Involutive (@antipode n) := by
  intro x
  funext i
  simp [antipode]

noncomputable def oddPart {n : ℕ} (f : Cube (Fin n) → ℝ) (x : Cube (Fin n)) : ℝ :=
  (f x - f (antipode x)) / 2
noncomputable def evenPart {n : ℕ} (f : Cube (Fin n) → ℝ) (x : Cube (Fin n)) : ℝ :=
  (f x + f (antipode x)) / 2

 theorem oddPart_bounded {n : ℕ} (f : Cube (Fin n) → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (x : Cube (Fin n)) :
    oddPart f x ∈ Set.Icc (-1 : ℝ) 1 := by
  have h1 := hf x
  have h2 := hf (antipode x)
  constructor <;> dsimp [oddPart] <;> linarith [h1.1,h1.2,h2.1,h2.2]

 theorem oddPart_mean {n : ℕ} (f : Cube (Fin n) → ℝ) : (𝔼 x, oddPart f x) = 0 := by
  have he : (𝔼 x, f (antipode x)) = 𝔼 x, f x := by
    exact Fintype.expect_equiv antipode_involutive.toPerm _ _ (fun _ => rfl)
  simp_rw [oddPart]
  rw [← Finset.expect_div, Finset.expect_sub_distrib, he]
  ring

 theorem sum_cutoffInfluences {n : ℕ} (K : ℕ) (f : Cube (Fin n) → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    (∑ i, cutoffInfluence K i f) ≤ K := by
  classical
  have hiden : (∑ i, cutoffInfluence K i f) =
      ∑ s : Cube (Fin n), if degree s ≤ K then (degree s : ℝ) * coefficient f s ^ 2 else 0 := by
    unfold cutoffInfluence
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro s _
    by_cases hs : degree s ≤ K
    · simp only [hs, and_true, ↓reduceIte]
      rw [← sum_filter]
      simp [degree, sum_const, nsmul_eq_mul]
    · simp [hs]
  rw [hiden]
  calc
    _ ≤ ∑ s : Cube (Fin n), (K : ℝ) * coefficient f s ^ 2 := by
      apply sum_le_sum
      intro s _
      split_ifs with hs
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (sq_nonneg _)
      · positivity
    _ = (K : ℝ) * ∑ s, coefficient f s ^ 2 := (mul_sum _ _ _).symm
    _ ≤ (K : ℝ) * 1 := mul_le_mul_of_nonneg_left (spectral_energy_le_one f hf) (Nat.cast_nonneg _)
    _ = _ := mul_one _

end OptimalMaxCut.LongCode

end

end OAI
