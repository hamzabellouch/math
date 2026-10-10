import OAI.MeasureTheory.Falconer.Radial.RadialZoomBounds
import OAI.MeasureTheory.Falconer.Geometry.FiniteScaleBall
import OAI.MeasureTheory.Falconer.Recursion.ProfileIncrementFrostman

namespace OAI

/-! # The actual cell normalization used by the middle radial interval -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem cell_normalization_map (ρ : Measure (Space d)) (p : ℕ) (c : Space d)
    {b : ℝ} (hb : 0 < b) :
    Measure.map (radialZoom (b*(2:ℝ)^p) (by positivity) c) ρ =
      Measure.map (radialZoom b hb.ne' 0) (Measure.map (cellScaleMap p c) ρ) := by
  rw [Measure.map_map (radialZoom b hb.ne' 0).measurable (cellScaleMap_continuous p c).measurable]
  congr 1
  ext x
  simp only [Function.comp_apply,radialZoom_apply,cellScaleMap,sub_zero,smul_smul]

theorem cell_normalization_support (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (P : CellPath d) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ z ∂Measure.map (radialZoom (b*(2:ℝ)^P.length) (by positivity) (Q.descendant P).center)
      (ProbabilityTheory.cond ρ (Q.descendant P).carrier), ‖z‖ ≤ b*Real.sqrt d := by
  rw [cell_normalization_map _ _ _ hb]
  apply radialZoom_ae_bound _ hb 0
  simpa only [sub_zero] using rescaled_conditional_support Q hQ ρ P

theorem cell_normalization_quarter_point (Q : DyadicCube d) (hQ : Q.side = 1)
    (P : CellPath d) {b : ℝ} (hb : 0 < b) (hsmall : b*Real.sqrt d ≤ 1/4)
    {z : Space d} (hz : z ∈ (Q.descendant P).carrier) :
    ‖z-(Q.descendant P).center‖ ≤ 1/(4*(b*(2:ℝ)^P.length)) := by
  have hh := rescaled_cell_norm_bound Q hQ P hz
  rw [cellScaleMap,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2:ℝ)^P.length)] at hh
  have hm := (mul_le_mul_of_nonneg_left hh hb.le).trans hsmall
  apply (le_div_iff₀ (by positivity : 0 < 4*(b*(2:ℝ)^P.length))).mpr
  nlinarith

theorem conditional_frostman_coefficient_ge_one (d N : ℕ) {s E lam : ℝ}
    (hs : 0 ≤ s) (hE : 0 ≤ E) (hlam : 0 ≤ lam) :
    1 ≤ (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
      ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam) := by
  have hdim : (1:ℝ) ≤ (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ) := by
    exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ 2*Nat.ceil (2+4*Real.sqrt d)+1) :
      1 ≤ (2*Nat.ceil (2+4*Real.sqrt d)+1)^d)
  have htwo : 1 ≤ (2:ℝ)^s := Real.one_le_rpow (by norm_num) hs
  have hR : 1 ≤ ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam) :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hdim htwo) hR

theorem sourceClass_normalized_conditional_frostman (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E b : ℝ} (hs : 0 ≤ s) (hE : 0 ≤ E) (hlam : 0 ≤ lam)
    (hb : 0 < b) (hb1 : b ≤ 1) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) :
    ∀ x : Space d, ∀ r : ℝ, 0 < r → 1/(2:ℝ)^(t-p) ≤ r →
      Measure.map (radialZoom (b*(2:ℝ)^p) (by positivity) (Q.descendant P).center)
        (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
        (Metric.ball x r) ≤
      ENNReal.ofReal (((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam))*b^(-s)*r^s) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hPpos
  intro x r hr hδ
  rw [cell_normalization_map _ _ _ hb]
  apply radialZoom_frostman_bound _ hb hb1
    (conditional_frostman_coefficient_ge_one d N hs hE hlam) hs (by simp) 0
    (sourceClass_conditional_frostman_of_increment Q hQ μ hN hB hs hwidth hlarge
      hp₀ hpt htN hP hPpos hinc) x r hr hδ

theorem sourceClass_scaled_dyadic_ball (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E b K : ℝ} (hs : 0 ≤ s) (hE : 0 ≤ E) (hlam : 0 ≤ lam)
    (hb : 0 < b) (hb1 : b ≤ 1) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t M : ℕ} (hpt : p ≤ t) (htN : t ≤ N) (hM : M ≤ t-p)
    {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p)
    (hcoef : (((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
      ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam))*b^(-s)) ≤ K) :
    ∀ x : Space d, ∀ j : ℕ, j ≤ M →
      ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier
        (Metric.ball x ((1/(2:ℝ)^j)/(b*(2:ℝ)^p))) ≤
          ENNReal.ofReal (K*(1/(2:ℝ)^j)^s) := by
  intro x j hj
  have ha : 0 < b*(2:ℝ)^p := by positivity
  have hr : 1/(2:ℝ)^(t-p) ≤ 1/(2:ℝ)^j :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (hj.trans hM))
  have hh := sourceClass_normalized_conditional_frostman Q hQ μ hN hB hs hE hlam hb hb1
    hwidth hlarge hp₀ hpt htN hP hPpos hinc
    (radialZoom (b*(2:ℝ)^p) ha.ne' (Q.descendant P).center x)
    (1/(2:ℝ)^j) (by positivity) hr
  rw [radialZoom_ball_apply _ ha] at hh
  have hc : (Q.descendant P).center+(b*(2:ℝ)^p)⁻¹ •
      radialZoom (b*(2:ℝ)^p) ha.ne' (Q.descendant P).center x = x := by
    simp only [radialZoom_apply,smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
    abel
  rw [hc] at hh
  apply hh.trans
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoef (by positivity))

end Falconer.Regularization

end OAI
