import OAI.NumberTheory.Jacobsthal.Primes.UniformDirichletBasepoint
import OAI.NumberTheory.Ostmann.Dirichlet.GrowthIntegral

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open MeasureTheory Set
open scoped Topology

namespace Ostmann.Dirichlet

noncomputable def characterPartialSum {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ (n : ZMod q)

noncomputable def dirichletPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)

noncomputable def partialSumKernel {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (t : ℝ) : ℂ :=
  characterPartialSum χ t * (t : ℂ) ^ (-(s + 1))

lemma norm_partialSumKernel_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖partialSumKernel χ s t‖ ≤ q * t ^ (-s.re - 1) := by
  rw [partialSumKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have he : (-(s + 1)).re = -s.re - 1 := by simp; ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (norm_sum_character_Icc_lt χ hχ ⌊t⌋₊).le
    (Real.rpow_nonneg ht.le _)

lemma integrableOn_partialSumKernel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (partialSumKernel χ s) (Ioi a) := by
  have hmeas : Measurable (characterPartialSum χ) :=
    (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q))).comp
      Nat.measurable_floor
  have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi a) := by
    intro t ht
    exact ((differentiableAt_id.ofReal_cpow_const (ha.trans ht).ne'
      (by intro h; have := congrArg Complex.re h; simp at this; linarith)).continuousAt).continuousWithinAt
  apply ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) ha).const_mul (q : ℝ)).mono'
    (hmeas.aestronglyMeasurable.mul (hc.aestronglyMeasurable measurableSet_Ioi))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_partialSumKernel_le χ hχ s (ha.trans ht)

lemma sum_Icc_zero_eq_sum_Icc_one {α : Type*} [AddCommMonoid α] (f : ℕ → α)
    (hf : f 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.Icc 0 N, f n = ∑ n ∈ Finset.Icc 1 N, f n := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N),
    Finset.sum_insert (by simp), hf, zero_add, zero_add]

lemma dirichletPolynomial_eq_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    dirichletPolynomial χ N s =
      (N : ℂ) ^ (-s) * characterPartialSum χ N +
        s * ∫ t : ℝ in Ioc 1 (N : ℝ), partialSumKernel χ s t := by
  have hzero : χ ((0 : ℕ) : ZMod q) = 0 := by
    simpa using χ.map_zero' (hχ ∘ χ.level_one')
  have hsn : -s ≠ 0 := neg_ne_zero.mpr (Complex.ne_zero_of_re_pos hs)
  have hd : ∀ t ∈ Icc (1 : ℝ) N,
      DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ (-s)) t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht.1).ne' hsn
  have hi : IntegrableOn (deriv fun x : ℝ => (x : ℂ) ^ (-s)) (Icc (1 : ℝ) N) :=
    (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one (by simpa using neg_neg_of_pos hs))).mono_set
        (fun _ ht => ht.1)
  have hab := sum_mul_eq_sub_integral_mul₀' (fun n => χ (n : ZMod q)) hzero N hd hi
  have hzero' : χ (0 : ZMod q) = 0 := by simpa using hzero
  rw [sum_Icc_zero_eq_sum_Icc_one _ (by simp [hzero'])] at hab
  simp_rw [sum_Icc_zero_eq_sum_Icc_one (fun n : ℕ => χ (n : ZMod q)) hzero] at hab
  have hder : (∫ t : ℝ in Ioc 1 (N : ℝ),
      deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) =
      -s * ∫ t : ℝ in Ioc 1 (N : ℝ), partialSumKernel χ s t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [Complex.deriv_ofReal_cpow_const (zero_lt_one.trans ht.1).ne' hsn]
    simp only [partialSumKernel, characterPartialSum]
    rw [show -s - 1 = -(s + 1) by ring]
    ring
  rw [hder] at hab
  simpa only [dirichletPolynomial, characterPartialSum, Nat.floor_natCast, Complex.ofReal_natCast, sub_neg_eq_add,
    neg_mul, mul_comm (χ _) ((_:ℂ)^(-s))] using hab

end Ostmann.Dirichlet

end OAI
