import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter

namespace OrdinaryCorrelations.NonpretentiousEuler
open Finset

lemma norm_one_add_le_exp (z : ℂ) :
    ‖1 + z‖ ≤ Real.exp (z.re + ‖z‖ ^ 2 / 2) := by
  have hn : ‖1 + z‖ ^ 2 = 1 + 2 * z.re + ‖z‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have he := Real.add_one_le_exp (2 * z.re + ‖z‖ ^ 2)
  have he2 : (Real.exp (z.re + ‖z‖ ^ 2 / 2)) ^ 2 = Real.exp (2 * z.re + ‖z‖ ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
  rw [he2, hn]
  linarith

lemma norm_one_add_div_le_exp (z : ℂ) {p : ℕ} (hp : 0 < p) (hz : ‖z‖ ≤ 1) :
    ‖1 + z / (p : ℂ)‖ ≤ Real.exp (z.re / p + (p : ℝ)⁻¹ ^ 2 / 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hz0 := norm_nonneg z
  have hnorm : ‖z / (p : ℂ)‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_div, Complex.norm_natCast, inv_eq_one_div]
    exact div_le_div_of_nonneg_right hz hp0.le
  refine (norm_one_add_le_exp (z / (p : ℂ))).trans (Real.exp_le_exp.mpr ?_)
  have hre : (z / (p : ℂ)).re = z.re / p := by
    simp
  rw [hre]
  gcongr

def twist (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (p : ℕ) : ℂ :=
  f p * star (χ (p : ZMod q) * Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))

lemma twist_norm_le {f : ℕ → ℂ} (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (p : ℕ) : ‖twist f χ t p‖ ≤ 1 := by
  unfold twist
  rw [norm_mul, norm_star, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, sub_self, Real.exp_zero, mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hf p)).trans (χ.norm_le_one _)

lemma distanceSq_nonneg {f : ℕ → ℂ} (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t X : ℝ) : 0 ≤ distanceSq f χ t X := by
  apply sum_nonneg
  intro p _
  apply div_nonneg _ (Nat.cast_nonneg _)
  have hh := (Complex.re_le_norm (twist f χ t p)).trans (twist_norm_le hf χ t p)
  exact sub_nonneg.mpr hh

def normalizedProduct (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) : ℂ :=
  ((Real.exp (-(∑ p ∈ (Icc 2 N).filter Nat.Prime, (p : ℝ)⁻¹))) : ℂ) *
    ∏ p ∈ (Icc 2 N).filter Nat.Prime, (1 + twist f χ t p / (p : ℂ))

lemma prime_inv_sq_sum_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ (Icc 2 N).filter Nat.Prime, (p : ℝ)⁻¹ ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ p ∈ Ioc 1 N, (p : ℝ)⁻¹ ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have h := mem_Icc.mp (mem_filter.mp hp).1
        exact mem_Ioc.mpr ⟨by omega, h.2⟩
      · intros; positivity
    _ = ∑ p ∈ Ioc 1 N, ((p : ℝ) ^ 2)⁻¹ := by simp only [inv_pow]
    _ ≤ (1 : ℝ)⁻¹ - (N : ℝ)⁻¹ := by simpa using (sum_Ioc_inv_sq_le_sub (α := ℝ) (by decide) hN)
    _ ≤ 1 := by
      simp

theorem norm_normalizedProduct_le {f : ℕ → ℂ} (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ‖normalizedProduct f χ t N‖ ≤ Real.exp (1 - distanceSq f χ t N) := by
  let P := (Icc 2 N).filter Nat.Prime
  have hp : ∀ p ∈ P, 0 < p := fun p hp => (mem_filter.mp hp).2.pos
  have hprod : ‖∏ p ∈ P, (1 + twist f χ t p / (p : ℂ))‖ ≤
      Real.exp (∑ p ∈ P, ((twist f χ t p).re / p + (p : ℝ)⁻¹ ^ 2 / 2)) := by
    rw [norm_prod, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun prime _ => norm_nonneg _)
      (fun prime hprime => norm_one_add_div_le_exp _ (hp prime hprime)
        (twist_norm_le hf χ t prime))
  have hid : -(∑ p ∈ P, (p : ℝ)⁻¹) +
      ∑ p ∈ P, ((twist f χ t p).re / p + (p : ℝ)⁻¹ ^ 2 / 2) =
      -distanceSq f χ t N + (∑ p ∈ P, (p : ℝ)⁻¹ ^ 2) / 2 := by
    simp only [distanceSq, Nat.floor_natCast]
    change _ = -(∑ p ∈ P, (1 - (twist f χ t p).re) / p) + _
    rw [← sum_neg_distrib, ← sum_add_distrib, sum_div, ← sum_neg_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    rw [sub_div]
    ring
  unfold normalizedProduct
  change ‖(Real.exp (-(∑ p ∈ P, (p : ℝ)⁻¹)) : ℂ) * _‖ ≤ _
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (-(∑ p ∈ P, (p : ℝ)⁻¹)) *
        Real.exp (∑ p ∈ P, ((twist f χ t p).re / p + (p : ℝ)⁻¹ ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (-distanceSq f χ t N + (∑ p ∈ P, (p : ℝ)⁻¹ ^ 2) / 2) := by
      rw [← Real.exp_add, hid]
    _ ≤ Real.exp (1 - distanceSq f χ t N) := by
      exact Real.exp_le_exp.mpr (by have hb := prime_inv_sq_sum_le hN; dsimp [P]; linarith)

theorem eventual_uniformEuler_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (q : ℕ) (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, t ∈ Set.Icc (-(N : ℝ)) (N : ℝ) →
      ‖normalizedProduct f χ t N‖ ≤ ε := by
  have hmin := (hNP q hq χ).eventually
    (eventually_ge_atTop (max 1 (1 - Real.log ε)))
  filter_upwards [hmin, eventually_ge_atTop (1 : ℕ)] with N hNmin hN
  intro t ht
  have hbdd : BddBelow ((fun t : ℝ => distance f χ t (N : ℝ)) ''
      Set.Icc (-(N : ℝ)) (N : ℝ)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, _, rfl⟩
    exact Real.sqrt_nonneg _
  have hdist := hNmin.trans (csInf_le hbdd (Set.mem_image_of_mem _ ht))
  have hd1 : 1 ≤ distance f χ t (N : ℝ) := (le_max_left _ _).trans hdist
  have hdε : 1 - Real.log ε ≤ distance f χ t (N : ℝ) := (le_max_right _ _).trans hdist
  have hs : distance f χ t (N : ℝ) ^ 2 = distanceSq f χ t (N : ℝ) :=
    Real.sq_sqrt (distanceSq_nonneg hf χ t N)
  have hh : 1 - distanceSq f χ t (N : ℝ) ≤ Real.log ε := by nlinarith
  calc
    ‖normalizedProduct f χ t N‖ ≤ Real.exp (1 - distanceSq f χ t (N : ℝ)) :=
      norm_normalizedProduct_le hf χ t hN
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr hh
    _ = ε := Real.exp_log hε

theorem tendsto_normalizedProduct {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (q : ℕ) (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (t : ℕ → ℝ)
    (ht : ∀ N : ℕ, t N ∈ Set.Icc (-(N : ℝ)) (N : ℝ)) :
    Tendsto (fun N => normalizedProduct f χ (t N) N) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventual_uniformEuler_small hf hNP q hq χ (ε / 2) (by positivity))
  refine ⟨N₀, ?_⟩
  intro N hN
  simpa only [_root_.dist_zero_right] using
    (hN₀ N hN (t N) (ht N)).trans_lt (half_lt_self hε)

end OrdinaryCorrelations.NonpretentiousEuler

end

end OAI
