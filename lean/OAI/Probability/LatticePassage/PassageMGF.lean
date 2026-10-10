import OAI.Probability.LatticePassage.PassageVariance
import OAI.Probability.LatticePassage.ExponentialEnergy
import Mathlib.Probability.Moments.MGFAnalytic

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma integrable_localPassageTime_exp (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : a ≤ 1/2) :
    Integrable (fun ω => exp (a*localPassageTime ω x y R)) environmentLaw := by
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  apply (integrable_trail_exp p hp.isTrail).mono' (by fun_prop)
  filter_upwards [all_edge_weights_positive] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply exp_le_exp.mpr
  have hn := (passageTime_nonneg ω (fun e => (hω e).le) (lattice_walk x y)).trans
    (passageTime_le_localPassageTime ω (fun e => (hω e).le) x y R hR)
  have hb := localPassageTime_le_pathCost ω p hp (hl.trans_lt hR)
  nlinarith

lemma integrable_finitePassageTime_exp (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : a ≤ 1/2) :
    Integrable (fun v => exp (a*finitePassageTime x y R v))
      (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) := by
  have hg : AEStronglyMeasurable (fun u : ℝ => exp (a*u))
      (Measure.map (localPassageTime · x y R) environmentLaw) := by fun_prop
  have h₁ := integrable_map_measure (μ := environmentLaw) hg
    (measurable_localPassageTime x y R).aemeasurable
  rw [finitePassageTime_law] at h₁
  have h₂ := integrable_map_measure
    (μ := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))
    (g := fun u : ℝ => exp (a*u)) (by fun_prop)
    (measurable_finitePassageTime x y R).aemeasurable
  exact h₂.mp (h₁.mpr (integrable_localPassageTime_exp x y R hR a ha))

theorem finitePassageTime_mgf_recursion (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : |a| ≤ 1/2) :
    mgf (finitePassageTime x y R) (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) a ≤
      (mgf (finitePassageTime x y R) (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) (a/2))^2 +
      (4*a^2*R) * mgf (finitePassageTime x y R)
        (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) a := by
  classical
  let P := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)
  let F := finitePassageTime x y R
  let H := fun v => exp (a*F v/2)
  have hHmeas : Measurable H := by dsimp [H,F]; fun_prop
  have hExp : Integrable (fun v => exp (a*F v)) P :=
    integrable_finitePassageTime_exp x y R hR a (le_trans (le_abs_self a) ha)
  have hs : (fun v => (H v)^2) = fun v => exp (a*F v) := by
    funext v
    dsimp [H]
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hH : MemLp H 2 P := by
    apply (memLp_two_iff_integrable_sq hHmeas.aestronglyMeasurable).mpr
    rw [hs]
    exact hExp
  have henergy := finite_exponential_resampling_energy x y R hR a ha
  have hv : ENNReal.ofReal (variance H P) ≤ ENNReal.ofReal
      ((4*a^2*R)*(∫ v, exp (a*F v) ∂P)) := by
    rw [variance_eq_integral hHmeas.aemeasurable,
      ofReal_integral_eq_lintegral_ofReal
        (f := fun v => (H v - ∫ w, H w ∂P)^2)
        (hH.sub (memLp_const _)).integrable_sq (by filter_upwards [] with v; positivity)]
    apply (centered_square_lintegral_le_resampling (expMeasure 1) hHmeas
      (hH.integrable (by norm_num))).trans
    apply henergy.trans_eq
    rw [← ofReal_integral_eq_lintegral_ofReal hExp (by filter_upwards [] with v; positivity)]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4*a^2*R),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 4*a^2), ENNReal.ofReal_natCast]
  have hM : 0 ≤ ∫ v, exp (a*F v) ∂P := integral_nonneg (fun _ => (exp_pos _).le)
  have hv' := (ENNReal.ofReal_le_ofReal_iff (by positivity :
    0 ≤ (4*a^2*R)*(∫ v, exp (a*F v) ∂P))).mp hv
  rw [variance_eq_sub hH] at hv'
  simp only [Pi.pow_apply] at hv'
  rw [hs] at hv'
  have he : (∫ v, H v ∂P) = mgf F P (a/2) := by
    unfold mgf
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro v
    dsimp [H]
    congr 1
    ring
  rw [he] at hv'
  change mgf F P a ≤ (mgf F P (a/2))^2 + (4*a^2*R)*mgf F P a
  change mgf F P a - (mgf F P (a/2))^2 ≤ (4*a^2*R)*mgf F P a at hv'
  linarith

lemma neg_log_one_sub_le (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1/2) :
    -log (1-q) ≤ 2*q := by
  have hp : 0 < 1-q := by linarith
  have h := log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [log_inv] at h
  have hb : (1-q)⁻¹ - 1 ≤ 2*q := by
    rw [inv_eq_one_div]
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hp).mpr
    nlinarith
  exact h.trans hb

theorem finitePassageTime_cgf_recursion (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : |a| ≤ 1/2)
    (hq : 4*a^2*R ≤ 1/2) :
    cgf (finitePassageTime x y R) (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) a ≤
      2*cgf (finitePassageTime x y R) (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) (a/2)
        + 8*a^2*R := by
  let P := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)
  let F := finitePassageTime x y R
  have hM : 0 < mgf F P a := mgf_pos (integrable_finitePassageTime_exp x y R hR a
    ((le_abs_self a).trans ha))
  have hM2 : 0 < mgf F P (a/2) := mgf_pos (integrable_finitePassageTime_exp x y R hR (a/2)
    (by have := (le_abs_self a).trans ha; linarith))
  have hrec := finitePassageTime_mgf_recursion x y R hR a ha
  have hden : 0 < 1-4*a^2*R := by linarith
  have hr : mgf F P a ≤ (mgf F P (a/2))^2/(1-4*a^2*R) := by
    apply (le_div_iff₀ hden).mpr
    change mgf F P a ≤ (mgf F P (a/2))^2 + (4*a^2*R)*mgf F P a at hrec
    nlinarith
  have hl := log_le_log hM hr
  rw [log_div (pow_ne_zero _ hM2.ne') hden.ne', log_pow] at hl
  have hlog := neg_log_one_sub_le (4*a^2*R) (by positivity) hq
  change log (mgf F P a) ≤ 2*log (mgf F P (a/2)) + 8*a^2*R
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end CompanionFPP

end OAI
