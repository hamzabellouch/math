import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Supply.BivariateTruncation
open scoped BigOperators
open Complex Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def coefficientIntegral (r : ℝ) (n : ℕ) (f : ℂ → E) : E :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(0, r), (z⁻¹) ^ (n + 1) • f z

omit [CompleteSpace E] in
lemma norm_coefficientIntegral_le {r M : ℝ} (hr : 0 < r) (n : ℕ) (f : ℂ → E)
    (hM : ∀ z : ℂ, ‖z‖ = r → ‖f z‖ ≤ M) :
    ‖coefficientIntegral r n f‖ ≤ M / r ^ n := by
  have hb : ∀ z ∈ sphere (0 : ℂ) r,
      ‖(z⁻¹) ^ (n + 1) • f z‖ ≤ M / (r ^ n * r) := by
    intro z hz
    have hz' : ‖z‖ = r := by simpa [mem_sphere_iff_norm] using hz
    rw [norm_smul, norm_pow, norm_inv, hz', inv_pow, ← div_eq_inv_mul, pow_succ]
    exact (div_le_div_iff_of_pos_right (mul_pos (pow_pos hr n) hr)).2 (hM z hz')
  calc
    ‖coefficientIntegral r n f‖ ≤ r * (M / (r ^ n * r)) :=
      circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le hb
    _ = M / r ^ n := by field_simp

lemma weighted_monomial_eq (m n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (z⁻¹) ^ (n + 1) * z ^ m = z ^ ((m : ℤ) - n - 1) := by
  rw [inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_natCast, ← zpow_add₀ hz]
  congr 1
  push_cast
  omega

lemma coefficientIntegral_monomial {r : ℝ} (hr : 0 < r) (n m : ℕ) (a : E) :
    coefficientIntegral r n (fun z => z ^ m • a) = if m = n then a else 0 := by
  unfold coefficientIntegral
  have heq : (∮ z in C(0, r), (z⁻¹) ^ (n + 1) • z ^ m • a) =
      (∮ z in C(0, r), z ^ ((m : ℤ) - n - 1) • a) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      have hh : (0 : ℝ) = r := by simpa [h] using hz
      linarith
    dsimp
    rw [smul_smul, weighted_monomial_eq m n hz0]
  rw [heq, circleIntegral.integral_smul_const]
  by_cases hmn : m = n
  · subst m
    simp only [sub_self, zero_sub, zpow_neg_one, ↓reduceIte]
    have hi : (∮ z : ℂ in C(0, r), z⁻¹) = 2 * Real.pi * Complex.I := by
      simpa using circleIntegral.integral_sub_center_inv (0 : ℂ) hr.ne'
    rw [hi, inv_smul_smul₀ (by simp)]
  · rw [ite_eq_right hmn]
    have hpow : (m : ℤ) - n - 1 ≠ -1 := by omega
    have hi : (∮ z : ℂ in C(0, r), z ^ ((m : ℤ) - n - 1)) = 0 := by
      simpa using circleIntegral.integral_sub_zpow_of_ne hpow (0 : ℂ) (0 : ℂ) r
    rw [hi, zero_smul, smul_zero]

omit [CompleteSpace E] in
lemma weighted_monomial_circleIntegrable {r : ℝ} (hr : 0 < r) (n m : ℕ) (a : E) :
    CircleIntegrable (fun z : ℂ => (z⁻¹) ^ (n + 1) • z ^ m • a) 0 r := by
  apply ContinuousOn.circleIntegrable hr.le
  have hz0 : ∀ z ∈ sphere (0 : ℂ) r, z ≠ 0 := by
    intro z hz h
    have hh : (0 : ℝ) = r := by simpa [h] using hz
    linarith
  exact ((continuousOn_id.inv₀ hz0).pow _).smul
    ((continuousOn_id.pow _).smul continuousOn_const)

lemma coefficientIntegral_sum_monomials {α : Type*} (s : Finset α) (e : α → ℕ)
    (a : α → E) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    coefficientIntegral r n (fun z => ∑ x ∈ s, z ^ e x • a x) =
      ∑ x ∈ s, if e x = n then a x else 0 := by
  unfold coefficientIntegral
  simp only [Finset.smul_sum]
  rw [circleIntegral.integral_fun_sum (fun x hx =>
    weighted_monomial_circleIntegrable hr n (e x) (a x))]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact coefficientIntegral_monomial hr n (e x) (a x)

def eval (c : (ℕ × ℕ) →₀ E) (u v : ℂ) : E :=
  ∑ ij ∈ c.support, (u ^ ij.1 * v ^ ij.2) • c ij

def rectangularTruncation (c : (ℕ × ℕ) →₀ E) (K : ℕ) : E :=
  ∑ ij ∈ c.support.filter (fun ij => ij.1 ≤ K ∧ ij.2 ≤ K), c ij

lemma coefficientIntegral_eval_right (c : (ℕ × ℕ) →₀ E) {r : ℝ} (hr : 0 < r)
    (u : ℂ) (j : ℕ) :
    coefficientIntegral r j (eval c u) =
      ∑ ij ∈ c.support, u ^ ij.1 • (if ij.2 = j then c ij else 0) := by
  have heq : eval c u = fun v => ∑ ij ∈ c.support, v ^ ij.2 • (u ^ ij.1 • c ij) := by
    funext v
    simp only [eval, smul_smul, mul_comm]
  rw [heq, coefficientIntegral_sum_monomials _ _ _ hr]
  apply Finset.sum_congr rfl
  intro ij hij
  split_ifs <;> simp

lemma coefficientIntegral_eval (c : (ℕ × ℕ) →₀ E) {r : ℝ} (hr : 0 < r)
    (i j : ℕ) :
    coefficientIntegral r i (fun u => coefficientIntegral r j (eval c u)) = c (i,j) := by
  simp_rw [coefficientIntegral_eval_right c hr]
  rw [coefficientIntegral_sum_monomials _ _ _ hr]
  have heq : (fun ij : ℕ × ℕ => if ij.1 = i then (if ij.2 = j then c ij else 0) else 0) =
      (fun ij => if ij = (i,j) then c ij else 0) := by
    funext ij
    simp only [Prod.ext_iff]
    split_ifs <;> simp_all
  rw [heq]
  by_cases hij : (i,j) ∈ c.support
  · simp [hij]
  · simp [hij, Finsupp.notMem_support_iff.mp hij]

theorem coefficient_norm_le (c : (ℕ × ℕ) →₀ E) {r M : ℝ} (hr : 0 < r)
    (hM : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = r → ‖eval c u v‖ ≤ M) (i j : ℕ) :
    ‖c (i,j)‖ ≤ M / r ^ (i + j) := by
  rw [← coefficientIntegral_eval c hr i j]
  calc
    ‖coefficientIntegral r i (fun u => coefficientIntegral r j (eval c u))‖ ≤
        (M / r ^ j) / r ^ i := by
      apply norm_coefficientIntegral_le hr
      intro u hu
      apply norm_coefficientIntegral_le hr
      intro v hv
      exact hM u v hu hv
    _ = M / r ^ (i + j) := by rw [div_div, pow_add, mul_comm (r ^ i)]

lemma geometric_pair_sum_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (s : Finset (ℕ × ℕ)) :
    (∑ ij ∈ s, t ^ (ij.1 + ij.2)) ≤ 1 / (1 - t) ^ 2 := by
  have hg := hasSum_geometric_of_lt_one ht0 ht1
  have hprod := hg.mul hg (hg.summable.mul_of_nonneg hg.summable
    (fun n => pow_nonneg ht0 n) (fun n => pow_nonneg ht0 n))
  calc
    (∑ ij ∈ s, t ^ (ij.1 + ij.2)) = ∑ ij ∈ s, t ^ ij.1 * t ^ ij.2 := by
      simp only [pow_add]
    _ ≤ ∑' ij : ℕ × ℕ, t ^ ij.1 * t ^ ij.2 :=
      hprod.summable.sum_le_tsum s (fun _ _ => by positivity)
    _ = 1 / (1 - t) ^ 2 := by rw [hprod.tsum_eq]; simp [pow_two, mul_inv_rev]

lemma geometric_pair_sum_fst_tail_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (s : Finset (ℕ × ℕ)) (K : ℕ) (hs : ∀ ij ∈ s, K ≤ ij.1) :
    (∑ ij ∈ s, t ^ (ij.1 + ij.2)) ≤ t ^ K / (1 - t) ^ 2 := by
  let shift : ℕ × ℕ → ℕ × ℕ := fun ij => (ij.1 - K, ij.2)
  have hinj : ∀ x ∈ s, ∀ y ∈ s, shift x = shift y → x = y := by
    intro x hx y hy h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have hxK := hs x hx
    have hyK := hs y hy
    apply Prod.ext
    · dsimp [shift] at h1
      omega
    · exact h2
  have heq : (∑ ij ∈ s, t ^ (ij.1 + ij.2)) =
      t ^ K * ∑ ij ∈ s.image shift, t ^ (ij.1 + ij.2) := by
    rw [Finset.mul_sum, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro ij hij
    dsimp [shift]
    rw [← pow_add]
    congr 1
    have := hs ij hij
    omega
  rw [heq]
  calc
    t ^ K * (∑ ij ∈ s.image shift, t ^ (ij.1 + ij.2)) ≤ t ^ K * (1 / (1 - t) ^ 2) :=
      mul_le_mul_of_nonneg_left (geometric_pair_sum_le ht0 ht1 _) (pow_nonneg ht0 _)
    _ = t ^ K / (1 - t) ^ 2 := by ring

lemma geometric_pair_sum_snd_tail_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (s : Finset (ℕ × ℕ)) (K : ℕ) (hs : ∀ ij ∈ s, K ≤ ij.2) :
    (∑ ij ∈ s, t ^ (ij.1 + ij.2)) ≤ t ^ K / (1 - t) ^ 2 := by
  have h := geometric_pair_sum_fst_tail_le ht0 ht1 (s.image Prod.swap) K (by
    intro ij hij
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hij
    exact hs p hp)
  simpa only [Finset.sum_image Prod.swap_injective.injOn, Prod.fst_swap, Prod.snd_swap,
    Nat.add_comm] using h

lemma geometric_rectangular_tail_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (s : Finset (ℕ × ℕ)) (K : ℕ) :
    (∑ ij ∈ s.filter (fun ij => ¬ (ij.1 ≤ K ∧ ij.2 ≤ K)), t ^ (ij.1 + ij.2)) ≤
      2 * t ^ K / (1 - t) ^ 2 := by
  have hfst := geometric_pair_sum_fst_tail_le ht0 ht1
    (s.filter (fun ij => K < ij.1)) K (by intro p hp; exact (Finset.mem_filter.mp hp).2.le)
  have hsnd := geometric_pair_sum_snd_tail_le ht0 ht1
    (s.filter (fun ij => K < ij.2)) K (by intro p hp; exact (Finset.mem_filter.mp hp).2.le)
  have hsplit :
      (∑ ij ∈ s.filter (fun ij => ¬ (ij.1 ≤ K ∧ ij.2 ≤ K)), t ^ (ij.1 + ij.2)) ≤
      (∑ ij ∈ s.filter (fun ij => K < ij.1), t ^ (ij.1 + ij.2)) +
      (∑ ij ∈ s.filter (fun ij => K < ij.2), t ^ (ij.1 + ij.2)) := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ij hij
    have ht : 0 ≤ t ^ (ij.1 + ij.2) := pow_nonneg ht0 _
    split_ifs <;> try omega
    all_goals linarith
  calc
    _ ≤ _ := hsplit
    _ ≤ t ^ K / (1 - t) ^ 2 + t ^ K / (1 - t) ^ 2 := add_le_add hfst hsnd
    _ = 2 * t ^ K / (1 - t) ^ 2 := by ring

omit [CompleteSpace E] in

lemma rectangularTruncation_add_tail (c : (ℕ × ℕ) →₀ E) (K : ℕ) :
    rectangularTruncation c K +
      (∑ ij ∈ c.support.filter (fun ij => ¬ (ij.1 ≤ K ∧ ij.2 ≤ K)), c ij) =
      eval c 1 1 := by
  simpa [rectangularTruncation, eval] using
    Finset.sum_filter_add_sum_filter_not c.support (fun ij => ij.1 ≤ K ∧ ij.2 ≤ K) c

theorem rectangularTruncation_error_le (c : (ℕ × ℕ) →₀ E) {r M : ℝ} (hr : 1 < r)
    (hM : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = r → ‖eval c u v‖ ≤ M) (K : ℕ) :
    ‖rectangularTruncation c K - eval c 1 1‖ ≤
      2 * M * (r⁻¹) ^ K / (1 - r⁻¹) ^ 2 := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have ht0 : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have ht1 : r⁻¹ < 1 := (inv_lt_one₀ hr0).mpr hr
  have hM0 : 0 ≤ M := by
    have hrnorm : ‖(r : ℂ)‖ = r := by simp [Complex.norm_real, abs_of_pos hr0]
    exact (norm_nonneg _).trans (hM r r hrnorm hrnorm)
  let s := c.support.filter (fun ij => ¬ (ij.1 ≤ K ∧ ij.2 ≤ K))
  have hidentity : rectangularTruncation c K - eval c 1 1 = -(∑ ij ∈ s, c ij) := by
    rw [← rectangularTruncation_add_tail c K]
    dsimp [s]
    abel
  rw [hidentity, norm_neg]
  calc
    ‖∑ ij ∈ s, c ij‖ ≤ ∑ ij ∈ s, ‖c ij‖ := norm_sum_le _ _
    _ ≤ ∑ ij ∈ s, M * (r⁻¹) ^ (ij.1 + ij.2) := by
      apply Finset.sum_le_sum
      intro ij hij
      simpa only [inv_pow, div_eq_mul_inv] using coefficient_norm_le c hr0 hM ij.1 ij.2
    _ = M * ∑ ij ∈ s, (r⁻¹) ^ (ij.1 + ij.2) := (Finset.mul_sum _ _ _).symm
    _ ≤ M * (2 * (r⁻¹) ^ K / (1 - r⁻¹) ^ 2) :=
      mul_le_mul_of_nonneg_left (geometric_rectangular_tail_le ht0 ht1 c.support K) hM0
    _ = 2 * M * (r⁻¹) ^ K / (1 - r⁻¹) ^ 2 := by ring

theorem rectangularTruncation_error_le_div (c : (ℕ × ℕ) →₀ E) {r M : ℝ} (hr : 1 < r)
    (hM : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = r → ‖eval c u v‖ ≤ M) (K : ℕ) :
    ‖rectangularTruncation c K - eval c 1 1‖ ≤
      2 * M / (r ^ K * (1 - 1 / r) ^ 2) := by
  simpa only [one_div, inv_pow, div_eq_mul_inv, mul_inv_rev, mul_assoc,
    mul_comm, mul_left_comm, mul_one, one_mul] using rectangularTruncation_error_le c hr hM K

end Ostmann.Supply.BivariateTruncation

end

end OAI
