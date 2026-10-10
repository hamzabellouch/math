import OAI.NumberTheory.JointDickman.Analysis.ZetaUniformSublog
import OAI.NumberTheory.JointDickman.Analysis.CharacterDistanceEuler

namespace OAI

/-! # Qualitative prime-phase separation on the full frequency range -/
namespace JointDickman
open Complex Filter Finset PublishedInputs
open scoped Topology

lemma principalDistance_eq_cosine (X t : ℝ) :
    primeDistanceSquared (characterArithmetic (1 : DirichletCharacter ℂ 1)) X t =
      ∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
        (1 - Real.cos (t * Real.log (p : ℝ))) / (p : ℝ) := by
  unfold primeDistanceSquared
  apply sum_congr rfl
  intro p hp
  rw [characterArithmetic_prime _ (mem_filter.mp hp).2]
  have hc : (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 := by
    rw [show (p : ZMod 1) = 1 from Subsingleton.elim _ _]; exact map_one _
  simp only [hc, one_mul, Complex.exp_re, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    neg_zero, add_zero, Real.exp_zero, Real.cos_neg]

/-- The full frequency range needs only qualitative divergence here; no
numerical Vinogradov--Korobov rate is asserted. -/
theorem prime_cosine_defect_diverges (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 1 ≤ |t| → |t| ≤ 2*X →
      R ≤ ∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
        (1 - Real.cos (t * Real.log (p : ℝ))) / (p : ℝ) := by
  obtain ⟨C,hC⟩ := characterDistance_ge_log_sub_L
  let η := Real.exp (-(R+C+1))
  have hη : 0 < η := Real.exp_pos _
  filter_upwards [zeta_uniform_sublog hη,
    eventually_ge_atTop (max 2 (Real.exp 1))] with X hbound hX
  intro t htlo ht
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hlog1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hXe
  have hlog : 0 < Real.log X := by linarith
  have hs : 1 < (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I).re := by
    simp only [add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,sub_zero,zero_mul,add_zero]
    linarith [one_div_pos.mpr hlog]
  have hn : 0 < ‖riemannZeta (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs)
  have hl := Real.log_le_log hn (hbound t htlo ht)
  rw [Real.log_mul hη.ne' hlog.ne'] at hl
  dsimp only [η] at hl
  rw [Real.log_exp] at hl
  have hd := hC 1 (1 : DirichletCharacter ℂ 1) X hX t
  rw [DirichletCharacter.LFunction_modOne_eq, principalDistance_eq_cosine] at hd
  linarith

lemma cosine_defect_le_four_abs_defect (v : ℝ) :
    1 - Real.cos v ≤ 4 * (1 - |Real.cos (v/2)|) := by
  have hc := Real.cos_two_mul (v/2)
  rw [show 2*(v/2) = v by ring] at hc
  have ha := sq_abs (Real.cos (v/2))
  nlinarith [sq_nonneg (1 - |Real.cos (v/2)|)]

/-- This is the qualitative two-twist repulsion needed for short averages.
It includes the range up to twice the cutoff and has no analytic hypothesis. -/
theorem prime_abs_cosine_defect_diverges (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 1 ≤ |t| → |t| ≤ 2*X →
      R ≤ ∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
        (1 - |Real.cos (t * Real.log (p : ℝ) / 2)|) / (p : ℝ) := by
  filter_upwards [prime_cosine_defect_diverges (4*R)] with X hX
  intro t htlo ht
  have hsum : (∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
      (1 - Real.cos (t * Real.log (p : ℝ))) / (p : ℝ)) ≤
      4 * ∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
        (1 - |Real.cos (t * Real.log (p : ℝ) / 2)|) / (p : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p _
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
      (cosine_defect_le_four_abs_defect (t * Real.log (p : ℝ))) (Nat.cast_nonneg p)
  linarith [hX t htlo ht]

end JointDickman

end OAI
