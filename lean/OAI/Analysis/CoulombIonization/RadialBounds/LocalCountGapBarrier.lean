import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.Restriction

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped NNReal Topology BigOperators

namespace CoulombAnalysis

def countPlateau (a : ℝ) (x : TFSpace) : ℝ :=
  max 0 (min 1 ((2*a-‖x‖)/a))

lemma countPlateau_nonneg (a : ℝ) (x : TFSpace) : 0 ≤ countPlateau a x :=
  le_max_left _ _

lemma countPlateau_le_one (a : ℝ) (x : TFSpace) : countPlateau a x ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

lemma countPlateau_one {a : ℝ} (ha : 0 < a) {x : TFSpace} (hx : ‖x‖ ≤ a) :
    countPlateau a x = 1 := by
  have hh : 1 ≤ (2*a-‖x‖)/a := (le_div_iff₀ ha).mpr (by linarith)
  simp only [countPlateau,min_eq_left hh,max_eq_right (by norm_num : (0:ℝ) ≤ 1)]

lemma countPlateau_support {a : ℝ} (ha : 0 < a) :
    Function.support (countPlateau a) ⊆ closedBall 0 (2*a) := by
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra hn
  have hh : (2*a-‖x‖)/a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
  exact hx (max_eq_left ((min_le_right _ _).trans hh))

lemma countPlateau_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzWith ⟨a⁻¹, inv_nonneg.mpr ha.le⟩ (countPlateau a) := by
  have hh : LipschitzWith ⟨a⁻¹, inv_nonneg.mpr ha.le⟩
      (fun x : TFSpace => (2*a-‖x‖)/a) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have he : (2*a-‖x‖)/a-(2*a-‖y‖)/a = (‖y‖-‖x‖)/a := by ring
    rw [he,abs_div,abs_of_pos ha]
    have hd : |‖y‖-‖x‖| ≤ dist x y := by
      simpa only [dist_eq_norm,norm_sub_rev] using abs_norm_sub_norm_le y x
    change |‖y‖-‖x‖|/a ≤ a⁻¹*dist x y
    simpa only [inv_mul_eq_div] using div_le_div_of_nonneg_right hd ha.le
  exact (hh.const_min 1).const_max 0

lemma countPlateau_mul_integrable {R a : ℝ} (ha : 0 < a)
    (σ : TFLp (ballMeasure R)) :
    Integrable (fun x => countPlateau a x*σ x) (ballMeasure R) := by
  apply ((Lp.memLp σ).integrable (Fact.out : (1:ENNReal) ≤ 5/3)).bdd_mul
    (countPlateau_lipschitz ha).continuous.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (countPlateau_nonneg a x)]
    exact countPlateau_le_one a x

lemma countPlateau_mass_lower {R a : ℝ} (ha : 0 < a)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) :
    (∫ x in ball 0 a, σ x ∂ballMeasure R) ≤
      ∫ x, countPlateau a x*σ x ∂ballMeasure R := by
  have hi := (Lp.memLp σ).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  rw [←integral_indicator measurableSet_ball]
  apply integral_mono_ae (hi.indicator measurableSet_ball) (countPlateau_mul_integrable ha σ)
  filter_upwards [hσ] with x hx
  by_cases hb : x ∈ ball (0:TFSpace) a
  · rw [indicator_of_mem hb,countPlateau_one ha (mem_ball_zero_iff.mp hb).le,one_mul]
  · rw [indicator_of_notMem hb]
    exact mul_nonneg (countPlateau_nonneg a x) hx

lemma countPlateau_mass_upper {R a C : ℝ} (ha : 0 < a) (hR : 2*a < R)
    {f : TFLp (ballMeasure R)} (hC : 0 ≤ C)
    (hc : ∀ᵐ x ∂ballMeasure R, ‖x‖ ≤ 2*a → f x ≤ C) :
    (∫ x, countPlateau a x*f x ∂ballMeasure R) ≤
      C*((2*a)^3*(Real.pi*4/3)) := by
  have hi : Integrable (fun x : TFSpace => (closedBall 0 (2*a)).indicator (fun _ => C) x)
      (ballMeasure R) := (integrable_const C).indicator measurableSet_closedBall
  have hb : (∫ x, countPlateau a x*f x ∂ballMeasure R) ≤
      ∫ x, (closedBall (0:TFSpace) (2*a)).indicator (fun _ => C) x ∂ballMeasure R := by
    apply integral_mono_ae (countPlateau_mul_integrable ha f) hi
    filter_upwards [hc] with x hx
    by_cases hs : x ∈ closedBall (0:TFSpace) (2*a)
    · rw [indicator_of_mem hs]
      exact (mul_le_mul_of_nonneg_left (hx (mem_closedBall_zero_iff.mp hs))
        (countPlateau_nonneg a x)).trans (mul_le_of_le_one_left hC (countPlateau_le_one a x))
    · rw [indicator_of_notMem hs]
      have hz : countPlateau a x = 0 := Function.notMem_support.mp
        (fun hh => hs (countPlateau_support ha hh))
      simp only [hz,zero_mul,le_refl]
  rw [integral_indicator measurableSet_closedBall,setIntegral_const,smul_eq_mul] at hb
  have he : (ballMeasure R).real (closedBall (0:TFSpace) (2*a)) =
      volume.real (closedBall (0:TFSpace) (2*a)) := by
    rw [Measure.real,Measure.real,ballMeasure,Measure.restrict_apply measurableSet_closedBall]
    rw [inter_eq_left.mpr (closedBall_subset_ball hR)]
  rw [he,tfSpace_closedBall_real (2*a) (by positivity)] at hb
  simpa only [mul_comm C] using hb

theorem local_mass_sq_le_gap {R a C : ℝ} (ha : 0 < a) (hR : 4*a < R)
    (T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) (hC : 0 ≤ C)
    (hc : ∀ᵐ x ∂ballMeasure R, ‖x‖ ≤ 2*a → tfPatchMinimizer R T hT Φ x ≤ C) :
    (∫ x in ball 0 a, σ x ∂ballMeasure R)^2 ≤
      2*(C*((2*a)^3*(Real.pi*4/3)))^2+256*a*tfPatchGap R T hT Φ σ := by
  let f := tfPatchMinimizer R T hT Φ
  let q := ∫ x, countPlateau a x*σ x ∂ballMeasure R
  let p := ∫ x, countPlateau a x*f x ∂ballMeasure R
  let m := ∫ x in ball 0 a, σ x ∂ballMeasure R
  let D := C*((2*a)^3*(Real.pi*4/3))
  have hm : 0 ≤ m := integral_nonneg_of_ae (ae_restrict_of_ae hσ)
  have hmq : m ≤ q := countPlateau_mass_lower ha hσ
  have hp : p ≤ D := countPlateau_mass_upper ha (by linarith) hC hc
  have hdiff : (∫ x, countPlateau a x*(σ-f) x ∂ballMeasure R) = q-p := by
    rw [integral_congr_ae ((Lp.coeFn_sub σ f).mono fun x hx => by
      change (σ-f) x = σ x-f x at hx
      rw [hx,mul_sub])]
    exact integral_sub (countPlateau_mul_integrable ha σ) (countPlateau_mul_integrable ha f)
  have hh := tfPatchGap_lipschitz_control (r := 2*a) (by positivity) (by linarith)
    T hT Φ hσ (countPlateau_lipschitz ha) (countPlateau_support ha)
  change (∫ x, countPlateau a x*(σ-f) x ∂ballMeasure R)^2 ≤ _ at hh
  rw [hdiff] at hh
  have he : 16*(2*a)^3*(a⁻¹)^2 = 128*a := by
    field_simp [ha.ne']
    ring
  change (q-p)^2 ≤ (16*(2*a)^3*(a⁻¹)^2)*tfPatchGap R T hT Φ σ at hh
  rw [he] at hh
  have hmd : m ≤ D+(q-p) := by linarith
  have hs := mul_self_le_mul_self hm hmd
  have hsq := sq_nonneg (D-(q-p))
  change m^2 ≤ 2*D^2+256*a*tfPatchGap R T hT Φ σ
  nlinarith

end CoulombAnalysis

end

end OAI
