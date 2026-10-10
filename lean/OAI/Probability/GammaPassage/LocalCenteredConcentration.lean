import OAI.Probability.GammaPassage.LocalCenteredCGF
import OAI.Probability.GammaPassage.ConcentrationScale
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

namespace OAI

namespace GammaFPP.FiniteLocal
open MeasureTheory ProbabilityTheory PlanarFPP Real
open scoped ENNReal

/-- For every real threshold t, finite local fluctuations have a centered
sqrt(R)-scale exponential tail. The scale is positive for every rate>0. -/
theorem finitePassageTime_centered_exponential {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (t : ℝ) :
    (finiteGammaMeasure shape rate)
      {v | t*sqrt R ≤ |finitePassageTime p q R v -
        ∫ w, finitePassageTime p q R w ∂finiteGammaMeasure shape rate|} ≤
      2*ENNReal.ofReal (exp (1-concentrationKappa shape rate*t)) := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  let P := finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate
  let : IsProbabilityMeasure P := by dsimp [P, finiteGammaMeasure]; infer_instance
  let F := finitePassageTime p q R
  let M := ∫ v, F v ∂P
  let B : ℝ := 16*(2 : ℝ)^shape/rate^2
  let k := concentrationKappa shape rate
  let a : ℝ := k/sqrt R
  obtain ⟨hk, hkr, hkquarter, hkB⟩ := concentrationKappa_bounds (shape := shape) hr
  have hkB' : B*k^2 ≤ 1/16 := hkB
  have hpos : 0 < R := lt_of_le_of_lt (Nat.zero_le _) hR
  have hsqrt : 0 < sqrt R := sqrt_pos.mpr (by exact_mod_cast hpos)
  have hsqrt1 : 1 ≤ sqrt R := by
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hpos
    nlinarith [sq_sqrt (Nat.cast_nonneg R), sqrt_nonneg (R : ℝ)]
  have ha : 0 < a := div_pos hk hsqrt
  have hak : a ≤ k := by
    apply (div_le_iff₀ hsqrt).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt1 hk.le
  have har : a ≤ rate/4 := hak.trans hkr
  have has : a*sqrt R = k := by dsimp [a]; field_simp [hsqrt.ne']
  have hscale : B*a^2*R = B*k^2 := by
    calc
      _ = B*(a*sqrt R)^2 := by rw [mul_pow, sq_sqrt (Nat.cast_nonneg R)]; ring
      _ = _ := by rw [has]
  have hsmall : B*a^2*R ≤ 1/2 := by
    rw [hscale]
    linarith
  have hc := finitePassageTime_cgf_centered hs hr p q R hR a
    (by rwa [abs_of_pos ha]) hsmall
  have hcn := finitePassageTime_cgf_centered hs hr p q R hR (-a)
    (by simpa only [abs_neg, abs_of_pos ha] using har)
    (by simpa only [neg_sq] using hsmall)
  have hu : P.real {v | M+t*sqrt R ≤ F v} ≤ exp (1-k*t) := by
    apply (measure_ge_le_exp_cgf (μ := P) (X := F) (M+t*sqrt R) ha.le
      (integrable_finitePassageTime_exp hs hr p q R hR a (by linarith))).trans
    apply exp_le_exp.mpr
    change cgf F P a ≤ a*M+4*(B*a^2*R) at hc
    calc
      _ ≤ -a*(M+t*sqrt R)+(a*M+4*(B*a^2*R)) := add_le_add le_rfl hc
      _ = 4*(B*a^2*R)-t*(a*sqrt R) := by ring
      _ ≤ 1-k*t := by rw [hscale, has]; nlinarith
  have hl : P.real {v | F v ≤ M-t*sqrt R} ≤ exp (1-k*t) := by
    apply (measure_le_le_exp_cgf (μ := P) (X := F) (M-t*sqrt R)
      (neg_nonpos.mpr ha.le)
      (integrable_finitePassageTime_exp hs hr p q R hR (-a) (by linarith))).trans
    apply exp_le_exp.mpr
    change cgf F P (-a) ≤ (-a)*M+4*(B*(-a)^2*R) at hcn
    calc
      _ ≤ -(-a)*(M-t*sqrt R)+((-a)*M+4*(B*(-a)^2*R)) := add_le_add le_rfl hcn
      _ = 4*(B*a^2*R)-t*(a*sqrt R) := by ring
      _ ≤ 1-k*t := by rw [hscale, has]; nlinarith
  have hu' : P {v | M+t*sqrt R ≤ F v} ≤ ENNReal.ofReal (exp (1-k*t)) := by
    have hb := ENNReal.ofReal_le_ofReal hu
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hb
  have hl' : P {v | F v ≤ M-t*sqrt R} ≤ ENNReal.ofReal (exp (1-k*t)) := by
    have hb := ENNReal.ofReal_le_ofReal hl
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hb
  have hsub : {v | t*sqrt R ≤ |F v-M|} ⊆
      {v | M+t*sqrt R ≤ F v} ∪ {v | F v ≤ M-t*sqrt R} := by
    intro v hv
    change t*sqrt R ≤ |F v-M| at hv
    rcases le_total M (F v) with h | h
    · left
      change M+t*sqrt R ≤ F v
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hv
      linarith
    · right
      change F v ≤ M-t*sqrt R
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hv
      linarith
  change P {v | t*sqrt R ≤ |F v-M|} ≤ 2*ENNReal.ofReal (exp (1-k*t))
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  simpa only [two_mul] using add_le_add hu' hl'

end GammaFPP.FiniteLocal

end OAI
