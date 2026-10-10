import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.BrownianMartingales

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
namespace ExactSLEMain
theorem loewner_local_existence (A : ℝ) (b : ℝ≥0 → ℝ) (hb : Continuous b)
    (z : ℂ) (hz : 0 < z.im) : ∃ t : ℝ≥0, 0 < t ∧ alive A b t z := by
  let ε : ℝ := z.im / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  let L : ℝ := (|A| + 1) / ε
  have hL : 0 < L := div_pos (by positivity) hε
  let τ : ℝ := ε / L
  have hτ : 0 < τ := div_pos hε hL
  let v : ℝ → ℂ → ℂ := fun u x => (A : ℂ) / (x - (b u.toNNReal : ℂ))
  have hheight : ∀ x ∈ Metric.closedBall z ε, ε ≤ x.im := by
    intro x hx
    have hx' : ‖x - z‖ ≤ ε := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have hh := Complex.im_le_norm (z - x)
    rw [Complex.sub_im, norm_sub_rev] at hh
    dsimp [ε] at *
    linarith
  let εn : ℝ≥0 := ⟨ε, hε.le⟩
  let Ln : ℝ≥0 := ⟨L, hL.le⟩
  let Kn : ℝ≥0 := ⟨|A| / ε ^ 2, by positivity⟩
  let t₀ : Set.Icc (0 : ℝ) τ := ⟨0, ⟨le_rfl, hτ.le⟩⟩
  have hp : IsPicardLindelof v t₀ z εn 0 Ln Kn := by
    constructor
    · intro u hu
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      rw [dist_eq_norm, dist_eq_norm]
      exact loewner_vector_difference A (b u.toNNReal) ε hε x y (hheight x hx) (hheight y hy)
    · intro x hx
      apply Continuous.continuousOn
      apply Continuous.div continuous_const
        (continuous_const.sub (Complex.continuous_ofReal.comp (hb.comp continuous_real_toNNReal)))
      intro u
      have hi : 0 < (x - (b u.toNNReal : ℂ)).im := by
        simpa using hε.trans_le (hheight x hx)
      intro he
      change x - (b u.toNNReal : ℂ) = 0 at he
      rw [he] at hi
      simp at hi
    · intro u hu x hx
      change ‖(A : ℂ) / (x - (b u.toNNReal : ℂ))‖ ≤ L
      have hlo : ε ≤ ‖x - (b u.toNNReal : ℂ)‖ := by
        calc
          ε ≤ x.im := hheight x hx
          _ = (x - (b u.toNNReal : ℂ)).im := by simp
          _ ≤ _ := Complex.im_le_norm _
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      calc
        |A| / ‖x - (b u.toNNReal : ℂ)‖ ≤ |A| / ε :=
          div_le_div_of_nonneg_left (abs_nonneg _) hε hlo
        _ ≤ (|A| + 1) / ε := by gcongr; linarith
    · change L * max (τ - 0) (0 - 0) ≤ εn - (0 : ℝ≥0)
      simp only [sub_zero, max_eq_left hτ.le, NNReal.coe_zero, εn]
      dsimp [τ]
      rw [mul_div_cancel₀ _ hL.ne']
      exact le_rfl
  have hx : z ∈ Metric.closedBall z (0 : ℝ≥0) := by simp
  obtain ⟨f, hf⟩ := ODE.FunSpace.exists_isFixedPt_next hp hx
  have hinit : f.compProj t₀ = z := by
    rw [ODE.FunSpace.compProj_val, ← hf, ODE.FunSpace.next_apply₀]
  have hderiv : ∀ u ∈ Set.Icc (0 : ℝ) τ,
      HasDerivWithinAt f.compProj (v u (f.compProj u)) (Set.Icc 0 τ) u := by
    intro u hu
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hp.continuousOn_uncurry
      f.continuous_compProj.continuousOn
      (fun _ _ => f.compProj_mem_closedBall hp.mul_max_le) z hu |>.congr_of_mem _ hu
    intro u' hu'
    nth_rw 1 [← hf]
    rw [ODE.FunSpace.compProj_of_mem hu', ODE.FunSpace.next_apply]
  refine ⟨⟨τ, hτ.le⟩, hτ, f.compProj, hinit, ?_⟩
  intro u hu
  refine ⟨hε.trans_le (hheight _ (f.compProj_mem_closedBall hp.mul_max_le)), hderiv u hu⟩

end ExactSLEMain

 

open MeasureTheory Filter Set Metric Function ODE
open scoped NNReal Topology

namespace ExactSLEMain
open Set Metric

 
def heightClamp (ε : ℝ) (z : ℂ) : ℂ := ⟨z.re, max ε z.im⟩

lemma heightClamp_eq {ε : ℝ} {z : ℂ} (hz : ε ≤ z.im) : heightClamp ε z = z := by
  apply Complex.ext <;> simp [heightClamp, max_eq_right hz]

lemma heightClamp_lipschitz (ε : ℝ) : LipschitzWith 2 (heightClamp ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, dist_eq_norm]
  have hIm : LipschitzWith 1 Complex.im := LipschitzWith.of_dist_le_mul (fun z w => by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, _root_.one_mul, Complex.sub_im] using
      Complex.abs_im_le_norm (z-w))
  have him := (hIm.const_max ε).dist_le_mul z w
  have hre := Complex.abs_re_le_norm (z-w)
  have him' : |max ε z.im - max ε w.im| ≤ ‖z-w‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, _root_.one_mul] using him
  calc
    ‖heightClamp ε z - heightClamp ε w‖ ≤
        |(heightClamp ε z - heightClamp ε w).re| + |(heightClamp ε z - heightClamp ε w).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ‖z-w‖ + ‖z-w‖ := add_le_add hre him'
    _ = (2 : ℝ≥0) * ‖z-w‖ := by norm_num; ring

noncomputable def cutoffVector (A ε : ℝ) (z : ℂ) : ℂ := (A : ℂ) / heightClamp ε z

lemma cutoffVector_bound (A ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    ‖cutoffVector A ε z‖ ≤ |A|/ε := by
  rw [cutoffVector, norm_div, Complex.norm_real, Real.norm_eq_abs]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hε
    ((show ε ≤ (heightClamp ε z).im from le_max_left _ _).trans (Complex.im_le_norm _))

lemma cutoffVector_lipschitz (A ε : ℝ) (hε : 0 < ε) :
    LipschitzWith ⟨2*|A|/ε^2, by positivity⟩ (cutoffVector A ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, dist_eq_norm]
  have hv := loewner_vector_difference A 0 ε hε (heightClamp ε z) (heightClamp ε w)
    (le_max_left _ _) (le_max_left _ _)
  simp only [Complex.ofReal_zero, sub_zero] at hv
  calc
    ‖cutoffVector A ε z - cutoffVector A ε w‖ ≤
        (|A|/ε^2)*‖heightClamp ε z - heightClamp ε w‖ := hv
    _ ≤ (|A|/ε^2)*(2*‖z-w‖) := mul_le_mul_of_nonneg_left
      (by simpa only [dist_eq_norm, NNReal.coe_ofNat] using (heightClamp_lipschitz ε).dist_le_mul z w)
      (by positivity)
    _ = _ := by change _ = (2*|A|/ε^2)*‖z-w‖; ring

 

theorem exists_cutoff_loewner (A ε : ℝ) (hε : 0 < ε) (b : ℝ≥0 → ℝ)
    (hb : Continuous b) :
    ∃ F : ℝ≥0 → ℂ → ℂ,
      (∀ z, Continuous (fun t => F t z)) ∧
      (∀ z t, F t z = z + ∫ u in (0 : ℝ)..(t : ℝ),
        cutoffVector A ε (F u.toNNReal z - (b u.toNNReal : ℂ))) := by
  let L : ℝ≥0 := ⟨|A|/ε, by positivity⟩
  let K : ℝ≥0 := ⟨2*|A|/ε^2, by positivity⟩
  have hu : ∀ z : ℂ, Continuous (fun t : ℝ≥0 => -(b t : ℂ)) :=
    fun _ => (Complex.continuous_ofReal.comp hb).neg
  obtain ⟨F,hFc,hFm,hFe⟩ := ExactSLEFlow.measurable_additive_flow
    (cutoffVector A ε) L K (cutoffVector_lipschitz A ε hε)
    (cutoffVector_bound A ε hε) (fun t (_ : ℂ) => -(b t : ℂ)) hu
    (fun _ => measurable_const) id measurable_id
  exact ⟨F,hFc,by simpa only [id_eq, sub_eq_add_neg] using hFe⟩

lemma cutoff_loewner_hasDerivWithinAt {A ε : ℝ} (hε : 0 < ε)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) {F : ℝ≥0 → ℂ → ℂ}
    (hFc : ∀ z, Continuous (fun t => F t z))
    (hFe : ∀ z t, F t z = z + ∫ u in (0 : ℝ)..(t : ℝ),
      cutoffVector A ε (F u.toNNReal z - (b u.toNNReal : ℂ)))
    (z : ℂ) (T : ℝ≥0) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun u : ℝ => F u.toNNReal z)
      (cutoffVector A ε (F t.toNNReal z - (b t.toNNReal : ℂ))) (Icc (0 : ℝ) T) t := by
  simpa only [sub_eq_add_neg, Function.comp_def, Pi.neg_apply] using
    ExactSLEFlow.integral_flow_hasDerivWithinAt (cutoffVector_lipschitz A ε hε).continuous
      ((Complex.continuous_ofReal.comp hb).neg) (hFc z) (by
        simpa only [sub_eq_add_neg, Function.comp_def, Pi.neg_apply] using hFe z) T t ht

lemma cutoff_loewner_dist {A ε : ℝ} (hε : 0 < ε)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) {F : ℝ≥0 → ℂ → ℂ}
    (hFc : ∀ z, Continuous (fun t => F t z))
    (hFe : ∀ z t, F t z = z + ∫ u in (0 : ℝ)..(t : ℝ),
      cutoffVector A ε (F u.toNNReal z - (b u.toNNReal : ℂ)))
    (z w : ℂ) (T : ℝ≥0) :
    dist (F T z) (F T w) ≤ dist z w * Real.exp ((2*|A|/ε^2)*(T : ℝ)) := by
  have hd (z : ℂ) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :=
    (cutoff_loewner_hasDerivWithinAt hε hb hFc hFe z T t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hv (t : ℝ) : LipschitzWith ⟨2*|A|/ε^2, by positivity⟩
      (fun z : ℂ => cutoffVector A ε (z - (b t.toNNReal : ℂ))) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist (cutoffVector A ε (z - (b t.toNNReal : ℂ)))
      (cutoffVector A ε (w - (b t.toNNReal : ℂ))) ≤ (2*|A|/ε^2)*dist z w
    convert (cutoffVector_lipschitz A ε hε).dist_le_mul
      (z-(b t.toNNReal : ℂ)) (w-(b t.toNNReal : ℂ)) using 1
    simp only [dist_sub_right]
    rfl
  have h0 (z : ℂ) : F 0 z = z := by simpa using hFe z 0
  have hg := dist_le_of_trajectories_ODE hv
    ((hFc z).comp continuous_real_toNNReal).continuousOn (hd z)
    ((hFc w).comp continuous_real_toNNReal).continuousOn (hd w)
    (show dist (F (0 : ℝ).toNNReal z) (F (0 : ℝ).toNNReal w) ≤ dist z w by simp [h0])
    (T : ℝ) (show (T : ℝ) ∈ Icc (0 : ℝ) T by simp)
  change dist (F (T : ℝ).toNNReal z) (F (T : ℝ).toNNReal w) ≤
    dist z w * Real.exp ((2*|A|/ε^2)*((T : ℝ)-0)) at hg
  simpa only [Real.toNNReal_coe, sub_zero] using hg

end ExactSLEMain

namespace ExactSLEMain
open Set Metric
lemma cutoff_loewner_eq_solution {A ε : ℝ} (hε : 0 < ε)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) {F : ℝ≥0 → ℂ → ℂ}
    (hFc : ∀ z, Continuous (fun t => F t z))
    (hFe : ∀ z t, F t z = z + ∫ u in (0 : ℝ)..(t : ℝ),
      cutoffVector A ε (F u.toNNReal z - (b u.toNNReal : ℂ)))
    {z : ℂ} {T : ℝ≥0} {f : ℝ → ℂ} (hf : odeUntil A b z T f)
    (hlower : ∀ u ∈ Icc (0 : ℝ) T, ε ≤ (f u).im) :
    ∀ u ∈ Icc (0 : ℝ) T, F u.toNNReal z = f u := by
  have hfd := cutoff_loewner_hasDerivWithinAt hε hb hFc hFe z T
  have hgd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt f (cutoffVector A ε (f u + (-(b u.toNNReal : ℂ)))) (Icc (0 : ℝ) T) u := by
    have hc : heightClamp ε (f u - (b u.toNNReal : ℂ)) = f u - (b u.toNNReal : ℂ) :=
      heightClamp_eq (by simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hlower u hu)
    simpa only [cutoffVector, ← sub_eq_add_neg, hc] using (hf.2 u hu).2
  apply ExactSLEFlow.additive_flow_unique (cutoffVector_lipschitz A ε hε)
    ((hFc z).comp continuous_real_toNNReal).continuousOn (odeUntil_continuousOn hf)
    (fun u hu => by simpa only [sub_eq_add_neg,Function.comp_def] using hfd u hu) hgd
  simpa [hf.1, Function.comp_def] using hFe z 0

 

theorem loewner_local_cutoff {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} (hz : alive A b T z) :
    ∃ (ε δ : ℝ) (F : ℝ≥0 → ℂ → ℂ), 0 < ε ∧ 0 < δ ∧
      (∀ w, Continuous (fun t => F t w)) ∧
      (∀ w t, F t w = w + ∫ u in (0 : ℝ)..(t : ℝ),
        cutoffVector A ε (F u.toNNReal w - (b u.toNNReal : ℂ))) ∧
      (∀ w ∈ ball z δ, odeUntil A b w T (fun u => F u.toNNReal w)) ∧
      (∀ w ∈ ball z δ, ∀ u ≤ T, loewnerMap A b u w = F u w) ∧
      (∀ w ∈ ball z δ, ∀ u ≤ T, ε < (F u w).im) := by
  obtain ⟨f,hf⟩ := hz
  obtain ⟨η,hη,hmin⟩ := odeUntil_height_lower hf
  let ε := η/2
  have hε : 0 < ε := half_pos hη
  let K : ℝ := 2*|A|/ε^2
  let δ := ε / Real.exp (K*(T : ℝ))
  have hδ : 0 < δ := div_pos hε (Real.exp_pos _)
  obtain ⟨F,hFc,hFe⟩ := exists_cutoff_loewner A ε hε b hb
  have hFf := cutoff_loewner_eq_solution hε hb hFc hFe hf
    (fun u hu => (show ε ≤ η by dsimp [ε]; linarith).trans (hmin u hu))
  have hIm (w : ℂ) (hw : w ∈ ball z δ) (u : ℝ≥0) (hu : u ≤ T) : ε < (F u w).im := by
    have hd := cutoff_loewner_dist hε hb hFc hFe w z u
    have hdt : dist (F u w) (F u z) < ε := by
      calc
        dist (F u w) (F u z) ≤ dist w z * Real.exp (K*(u : ℝ)) := hd
        _ ≤ dist w z * Real.exp (K*(T : ℝ)) := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (show (u : ℝ) ≤ T from hu)
            (by dsimp [K]; positivity))) dist_nonneg
        _ < δ * Real.exp (K*(T : ℝ)) := mul_lt_mul_of_pos_right hw (Real.exp_pos _)
        _ = ε := div_mul_cancel₀ _ (Real.exp_ne_zero _)
    have him := Complex.im_le_norm (F u z - F u w)
    have hbase : η ≤ (F u z).im := by
      rw [show F u z = f u by simpa only [Real.toNNReal_coe] using hFf u ⟨u.coe_nonneg,hu⟩]
      exact hmin u ⟨u.coe_nonneg,hu⟩
    rw [Complex.sub_im, ← dist_eq_norm, dist_comm] at him
    dsimp [ε] at *
    linarith
  have hode (w : ℂ) (hw : w ∈ ball z δ) :
      odeUntil A b w T (fun u => F u.toNNReal w) := by
    refine ⟨by simpa using hFe w 0, fun u hu => ?_⟩
    have huT : u.toNNReal ≤ T := (Real.toNNReal_le_toNNReal hu.2).trans_eq (by simp)
    have hpos := hIm w hw u.toNNReal huT
    refine ⟨hε.trans hpos, ?_⟩
    have hd := cutoff_loewner_hasDerivWithinAt hε hb hFc hFe w T u hu
    have hc : heightClamp ε (F u.toNNReal w - (b u.toNNReal : ℂ)) =
        F u.toNNReal w - (b u.toNNReal : ℂ) :=
      heightClamp_eq (by simpa using hpos.le)
    simpa only [cutoffVector,hc] using hd
  refine ⟨ε,δ,F,hε,hδ,hFc,hFe,hode,?_,hIm⟩
  intro w hw u hu
  simpa only [Real.toNNReal_coe] using loewnerMap_eq (odeUntil_mono (hode w hw) hu)

lemma isOpen_alive {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b) (T : ℝ≥0) :
    IsOpen {z | alive A b T z} := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨ε,δ,F,hε,hδ,hFc,hFe,hode,hmap,hIm⟩ := loewner_local_cutoff hb hz
  exact ⟨δ,hδ,fun w hw => ⟨_,hode w hw⟩⟩

lemma continuousAt_loewnerMap {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {T : ℝ≥0} {z : ℂ} (hz : alive A b T z) : ContinuousAt (loewnerMap A b T) z := by
  obtain ⟨ε,δ,F,hε,hδ,hFc,hFe,hode,hmap,hIm⟩ := loewner_local_cutoff hb hz
  have hLip : LipschitzWith ⟨Real.exp ((2*|A|/ε^2)*(T : ℝ)), (Real.exp_pos _).le⟩ (F T) := by
    apply LipschitzWith.of_dist_le_mul
    intro w v
    change dist (F T w) (F T v) ≤ Real.exp ((2*|A|/ε^2)*(T : ℝ))*dist w v
    simpa only [_root_.mul_comm] using cutoff_loewner_dist hε hb hFc hFe w v T
  apply hLip.continuous.continuousAt.congr
  filter_upwards [Metric.ball_mem_nhds z hδ] with w hw
  exact (hmap w hw T le_rfl).symm

end ExactSLEMain

namespace ExactSLEMain
open Set

lemma scalar_linear_solution (H c : ℝ → ℂ) (hc : Continuous c) (T : ℝ≥0)
    (hH : ∀ u ∈ Icc (0 : ℝ) T, HasDerivWithinAt H (c u * H u) (Icc (0 : ℝ) T) u) :
    H T = H 0 * Complex.exp (∫ u in (0 : ℝ)..(T : ℝ), c u) := by
  let P : ℝ → ℂ := fun t => H t * Complex.exp (-(∫ u in (0 : ℝ)..t, c u))
  have hd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt P 0 (Icc (0 : ℝ) T) u := by
    have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 u)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    convert (hH u hu).mul (hi.neg.cexp.hasDerivWithinAt) using 1
    first | rfl | ring
  have hnorm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun u hu => by simp : ∀ u ∈ Icc (0 : ℝ) T, ‖(0 : ℂ)‖ ≤ 0)
    (convex_Icc (0 : ℝ) T) (show (0 : ℝ) ∈ Icc (0 : ℝ) T by simp)
    (show (T : ℝ) ∈ Icc (0 : ℝ) T by simp)
  have hp : P T = P 0 := sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm (by simpa only [zero_mul] using hnorm) (norm_nonneg _)))
  have he : H T * (Complex.exp (∫ u in (0 : ℝ)..(T : ℝ), c u))⁻¹ = H 0 := by
    simpa [P, Complex.exp_neg] using hp
  exact (mul_inv_eq_iff_eq_mul₀ (Complex.exp_ne_zero _)).mp he

lemma scalar_linear_solution_on (H c : ℝ → ℂ) (T : ℝ≥0)
    (hc : ContinuousOn c (Icc (0 : ℝ) T))
    (hH : ∀ u ∈ Icc (0 : ℝ) T, HasDerivWithinAt H (c u * H u) (Icc (0 : ℝ) T) u) :
    H T = H 0 * Complex.exp (∫ u in (0 : ℝ)..(T : ℝ), c u) := by
  let c' : ℝ → ℂ := fun u => c (projIcc (0 : ℝ) T T.coe_nonneg u)
  have hc' : Continuous c' := hc.domRestrict.comp continuous_projIcc
  have he (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : c' u = c u := by
    dsimp [c']; rw [projIcc_of_mem _ hu]
  have h := scalar_linear_solution H c' hc' T (fun u hu => by rw [he u hu]; exact hH u hu)
  rw [h]
  congr 2
  apply intervalIntegral.integral_congr
  intro u hu
  exact he u (by simpa only [uIcc_of_le T.coe_nonneg] using hu)

 
theorem loewner_solution_difference {A : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z w : ℂ} {T : ℝ≥0} {f g : ℝ → ℂ}
    (hf : odeUntil A b z T f) (hg : odeUntil A b w T g) :
    f T - g T = (z-w) * Complex.exp (∫ u in (0 : ℝ)..(T : ℝ),
      -(A : ℂ) / ((f u - (b u.toNNReal : ℂ)) * (g u - (b u.toNNReal : ℂ)))) := by
  let c : ℝ → ℂ := fun u => -(A : ℂ) /
    ((f u - (b u.toNNReal : ℂ)) * (g u - (b u.toNNReal : ℂ)))
  have hfn (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : f u - (b u.toNNReal : ℂ) ≠ 0 := by
    intro he
    have hy := (hf.2 u hu).1
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    linarith
  have hgn (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : g u - (b u.toNNReal : ℂ) ≠ 0 := by
    intro he
    have hy := (hg.2 u hu).1
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    linarith
  have hbc : Continuous (fun u : ℝ => (b u.toNNReal : ℂ)) :=
    Complex.continuous_ofReal.comp (hb.comp continuous_real_toNNReal)
  have hc : ContinuousOn c (Icc (0 : ℝ) T) := continuousOn_const.div
    (((odeUntil_continuousOn hf).sub hbc.continuousOn).mul
      ((odeUntil_continuousOn hg).sub hbc.continuousOn))
      (fun u hu => mul_ne_zero (hfn u hu) (hgn u hu))
  have hd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) : HasDerivWithinAt (fun u => f u-g u)
      (c u*(f u-g u)) (Icc (0 : ℝ) T) u := by
    convert (hf.2 u hu).2.sub (hg.2 u hu).2 using 1
    try rfl
    dsimp [c]
    field_simp [hfn u hu, hgn u hu]
    ring
  simpa only [hf.1,hg.1] using scalar_linear_solution_on (fun u => f u-g u) c T hc hd

end ExactSLEMain

namespace ExactSLEMain
open Set Metric

lemma heightClamp_norm_lower (ε : ℝ) (z : ℂ) : ε ≤ ‖heightClamp ε z‖ :=
  (show ε ≤ (heightClamp ε z).im from le_max_left _ _).trans (Complex.im_le_norm _)

lemma heightClamp_ne_zero {ε : ℝ} (hε : 0 < ε) (z : ℂ) : heightClamp ε z ≠ 0 :=
  norm_pos_iff.mp (hε.trans_le (heightClamp_norm_lower ε z))

lemma invprod_heightClamp_bound (A ε : ℝ) (hε : 0 < ε) (z w : ℂ) :
    ‖-(A : ℂ)/(heightClamp ε z * heightClamp ε w)‖ ≤ |A|/ε^2 := by
  rw [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,norm_mul]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hε)
    (by simpa only [pow_two] using (mul_le_mul (heightClamp_norm_lower ε z)
      (heightClamp_norm_lower ε w) hε.le (norm_nonneg _)))

lemma cutoff_loewner_continuous_start {A ε : ℝ} (hε : 0 < ε)
    {b : ℝ≥0 → ℝ} (hb : Continuous b) {F : ℝ≥0 → ℂ → ℂ}
    (hFc : ∀ z, Continuous (fun t => F t z))
    (hFe : ∀ z t, F t z = z + ∫ u in (0 : ℝ)..(t : ℝ),
      cutoffVector A ε (F u.toNNReal z - (b u.toNNReal : ℂ))) (T : ℝ≥0) :
    Continuous (F T) := by
  have hLip : LipschitzWith ⟨Real.exp ((2*|A|/ε^2)*(T : ℝ)), (Real.exp_pos _).le⟩ (F T) := by
    apply LipschitzWith.of_dist_le_mul
    intro w v
    change dist (F T w) (F T v) ≤ Real.exp ((2*|A|/ε^2)*(T : ℝ))*dist w v
    simpa only [_root_.mul_comm] using cutoff_loewner_dist hε hb hFc hFe w v T
  exact hLip.continuous

 

end ExactSLEMain
end

end OAI
