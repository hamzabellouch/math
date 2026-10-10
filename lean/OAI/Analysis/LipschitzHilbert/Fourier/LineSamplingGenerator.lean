import OAI.Analysis.LipschitzHilbert.Fourier.LineSamplingHomeomorph

namespace OAI

/-! The actual conjugation generator for a compact smooth direction.
Its Lipschitz bound is uniform in the short time parameter. -/
noncomputable section
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem lineSamplingHomeomorph_symm_contDiff (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)
    (t : ℝ) (ht : |t|≤1/2) :
    ContDiff ℝ ∞ ((lineSamplingHomeomorph u hu B hB hb t ht).symm : ℝ → ℝ) := by
  let e := lineSamplingHomeomorph u hu B hB hb t ht
  have hd : Differentiable ℝ u := hc.differentiable (by simp)
  have hne (x : ℝ) : 1-t*deriv u x≠0 := by
    have hu' : |deriv u x|≤1 := by
      simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀:=x) hu
    have hp : |t*deriv u x|≤1/2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hu' (abs_nonneg t)).trans (by simpa only [mul_one] using ht)
    have hl := (abs_le.mp hp).2
    linarith
  have he' (x : ℝ) : HasDerivAt e (1-t*deriv u x) x :=
    (hasDerivAt_id x).sub ((hd x).hasDerivAt.const_mul t)
  have he : ContDiff ℝ ∞ (e : ℝ → ℝ) := contDiff_id.sub (contDiff_const.mul hc)
  exact e.contDiff_symm_deriv hne he' he

def lineSamplingGenerator (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) (y : ℝ) : ℝ :=
  -u ((lineSamplingHomeomorph u hu B hB hb t ht).symm y)

theorem lineSamplingGenerator_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    LipschitzWith 2 (lineSamplingGenerator u hu B hB hb t ht) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (-u ((lineSamplingHomeomorph u hu B hB hb t ht).symm x))
    (-u ((lineSamplingHomeomorph u hu B hB hb t ht).symm y))≤(2:ℝ)*dist x y
  rw [dist_neg_neg]
  simpa only [one_mul,Function.comp_def,NNReal.coe_ofNat] using
    (hu.comp (lineSamplingHomeomorph_symm_lipschitz u hu B hB hb t ht)).dist_le_mul x y

theorem lineSamplingGenerator_contDiff (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)
    (t : ℝ) (ht : |t|≤1/2) :
    ContDiff ℝ ∞ (lineSamplingGenerator u hu B hB hb t ht) :=
  (hc.comp (lineSamplingHomeomorph_symm_contDiff u hu hc B hB hb t ht)).neg

theorem lineSamplingGenerator_compact (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hcompact : HasCompactSupport u) (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)
    (t : ℝ) (ht : |t|≤1/2) :
    HasCompactSupport (lineSamplingGenerator u hu B hB hb t ht) :=
  (hcompact.comp_homeomorph (lineSamplingHomeomorph u hu B hB hb t ht).symm).neg

def lineSamplingGeneratorSchwartz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) : SchwartzMap ℝ ℂ :=
  ((lineSamplingGenerator_compact u hu hcompact B hB hb t ht).toSchwartzMap
    (lineSamplingGenerator_contDiff u hu hc B hB hb t ht)).postcompCLM Complex.ofRealCLM

theorem lineSamplingGeneratorSchwartz_apply (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) (y : ℝ) :
    lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht y=
      (lineSamplingGenerator u hu B hB hb t ht y : ℂ) := rfl

theorem lineSamplingGeneratorSchwartz_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) (x y : ℝ) :
    ‖lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht x-
      lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht y‖≤2*|x-y| := by
  have hh := (lineSamplingGenerator_lipschitz u hu B hB hb t ht).dist_le_mul x y
  simpa only [lineSamplingGeneratorSchwartz_apply,←Complex.ofReal_sub,Complex.norm_real,
    Real.dist_eq,Real.norm_eq_abs,NNReal.coe_ofNat] using hh

theorem lineSamplingGenerator_commutator_bound (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    ‖lineDerivativeCommutatorL2 m (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht)‖≤
      2*lineCommutatorNormConstant*A := by
  have hh := lineDerivativeCommutatorL2_bound m
    (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht) A 2 hA hm
    (lineSamplingGeneratorSchwartz_lipschitz u hu hc hcompact B hB hb t ht)
  nlinarith only [hh]

end LipschitzHilbert.PacketRepresentation

end

end OAI
