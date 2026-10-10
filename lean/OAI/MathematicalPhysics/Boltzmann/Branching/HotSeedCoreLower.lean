import OAI.MathematicalPhysics.Boltzmann.Branching.RebuiltHotInitial
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarriers
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum
import OAI.MathematicalPhysics.Boltzmann.Jets.PeriodicJetFamilies
import Mathlib.MeasureTheory.Function.Floor

namespace OAI

section

/-! # A localized periodic thermal seed, normalized in the singular weighted norm -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.HotSeedProfile

def centered (x : ℝ) : ℝ := Int.fract (x+1/2)-1/2

def centeredSpace (x : Space) : Space :=
  (WithLp.toLp 2 (fun i => centered (x.1 i)),centered x.2)

def raw (q δ : ℝ) (p : JetPrototype.Phase) : ℝ :=
  JetThermalKernel.J (δ⁻¹ • PlaneChart.join (centeredSpace p.1).1 (centeredSpace p.1).2)*
    (JetThermalKernel.J p.2/H q p.2)

def bound : ℝ := JetThermalKernel.bound^2*Real.exp 2*tiltConstant

theorem bound_pos : 0 < bound := by
  unfold bound
  exact mul_pos (mul_pos (sq_pos_of_pos JetThermalKernel.bound_pos) (Real.exp_pos _)) tiltConstant_pos

theorem centered_sub_int (x : ℝ) (n : ℤ) : centered (x-n) = centered x := by
  unfold centered
  rw [show x-(n:ℝ)+1/2=x+1/2-n by ring,Int.fract_sub_intCast]

theorem centeredSpace_shift (n : JetLattice.Lattice) (p : JetPrototype.Phase) :
    centeredSpace (WeightedTranslation.shift (JetCopyDatum.displacement n) p).1 = centeredSpace p.1 := by
  apply Prod.ext
  · ext i
    exact centered_sub_int (p.1.1 i) (n i.castSucc)
  · exact centered_sub_int p.1.2 (n (Fin.last 2))

theorem raw_periodic (q δ : ℝ) (n : JetLattice.Lattice) (p : JetPrototype.Phase) :
    raw q δ (WeightedTranslation.shift (JetCopyDatum.displacement n) p) = raw q δ p := by
  unfold raw
  rw [centeredSpace_shift]
  rfl

theorem measurable_centered : Measurable centered :=
  ((measurable_id.add_const (1/2)).fract).sub_const (1/2)

theorem measurable_centeredSpace : Measurable centeredSpace := by
  apply Measurable.prodMk
  · apply (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.comp
    exact Measurable.of_eval (fun i => measurable_centered.comp
      (show Measurable (fun x : Space => x.1 i) from by fun_prop))
  · exact measurable_centered.comp measurable_snd

theorem measurable_raw (q δ : ℝ) : Measurable (raw q δ) := by
  have hjoin : Measurable (fun x : Space => PlaneChart.join x.1 x.2) :=
    split.symm.measurable.comp (measurable_snd.prodMk measurable_fst)
  exact (JetThermalKernel.J_smooth.continuous.measurable.comp
    ((hjoin.comp (measurable_centeredSpace.comp measurable_fst)).const_smul δ⁻¹)).mul
    ((JetThermalKernel.J_smooth.continuous.measurable.comp measurable_snd).div
      ((ChartKernel.measurable_H q).comp measurable_snd))

theorem raw_nonneg (q δ : ℝ) (p : JetPrototype.Phase) : 0 ≤ raw q δ p :=
  mul_nonneg (JetThermalKernel.J_nonneg _) (div_nonneg (JetThermalKernel.J_nonneg _) (H_nonneg _ _))

theorem velocity_bound (q : ℝ) (v : Velocity) :
    JetThermalKernel.J v/H q v ≤ JetThermalKernel.bound*Real.exp 2*tiltConstant := by
  by_cases hv : 1 ≤ ‖v‖
  · rw [JetThermalKernel.J_zero hv,zero_div]
    exact mul_nonneg (mul_nonneg JetThermalKernel.bound_pos.le (Real.exp_pos _).le) tiltConstant_pos.le
  · have hv2 : ‖v‖^2 ≤ 1 := by nlinarith [norm_nonneg v,lt_of_not_ge hv]
    have he : 1 ≤ Real.exp 2*Real.exp (-2*‖v‖^2) := by
      rw [← Real.exp_add,← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    apply (div_le_iff₀ (H_pos q v)).mpr
    calc
      _ ≤ JetThermalKernel.bound := JetThermalKernel.J_le v
      _ ≤ JetThermalKernel.bound*(Real.exp 2*Real.exp (-2*‖v‖^2)) :=
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left he JetThermalKernel.bound_pos.le
      _ ≤ JetThermalKernel.bound*(Real.exp 2*(tiltConstant*H q v)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (JetGaussianEscape.gaussian_le_hot q v) (Real.exp_pos _).le)
          JetThermalKernel.bound_pos.le
      _ = _ := by ring

theorem raw_le (q δ : ℝ) (p : JetPrototype.Phase) : raw q δ p ≤ bound := by
  unfold raw bound
  have h := mul_le_mul
    (JetThermalKernel.J_le (δ⁻¹ • PlaneChart.join (centeredSpace p.1).1 (centeredSpace p.1).2))
    (velocity_bound q p.2)
    (div_nonneg (JetThermalKernel.J_nonneg _) (H_nonneg _ _)) JetThermalKernel.bound_pos.le
  exact h.trans_eq (by ring)

def normalized (q δ : ℝ) (p : JetPrototype.Phase) : ℝ :=
  (δ/PhaseEssSup.size (raw q δ))*raw q δ p

theorem normalized_size {q δ : ℝ} (hδ : 0 ≤ δ) (hp : 0 < PhaseEssSup.size (raw q δ)) :
    PhaseEssSup.size (normalized q δ) = δ := by
  change PhaseEssSup.size (fun p => (δ/PhaseEssSup.size (raw q δ))*raw q δ p) = δ
  rw [PhaseEssSup.size_const_mul,abs_of_nonneg (div_nonneg hδ hp.le)]
  exact div_mul_cancel₀ δ hp.ne'

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # The localized thermal seed has positive essential weighted norm -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Metric
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem size_pos_of_positive_set {f : JetPrototype.Phase → ℝ} {R : ℝ}
    (hfm : Measurable f) (hb : ∀ p, |f p| ≤ R) {s : Set JetPrototype.Phase}
    (hs : FlightMeasure.phaseVolume s ≠ 0) (hf : ∀ p ∈ s, 0 < f p) : 0 < size f := by
  obtain ⟨p,hp,hbound⟩ := exists_mem_of_measure_ne_zero_of_ae hs
    (ae_restrict_of_ae (ae_abs_le_size hfm hb))
  exact (hf p hp).trans_le ((le_abs_self _).trans hbound)

end BoltzmannNonuniqueness.PhaseEssSup

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem centered_eq {x : ℝ} (hx : |x| < 1/2) : centered x = x := by
  have h := abs_lt.mp hx
  unfold centered
  rw [Int.fract_eq_self.mpr ⟨by linarith [h.1],by linarith [h.2]⟩]
  ring

theorem centeredSpace_eq {x : Space} (hx : ‖x‖ < 1/2) : centeredSpace x = x := by
  apply Prod.ext
  · ext i
    apply centered_eq
    exact (show |x.1 i| ≤ ‖x.1‖ from by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x.1 i).trans_lt
      ((norm_fst_le x).trans_lt hx)
  · apply centered_eq
    exact (show |x.2| ≤ ‖x‖ from by simpa only [Real.norm_eq_abs] using norm_snd_le x).trans_lt hx

theorem J_pos {v : Velocity} (hv : ‖v‖ < 1) : 0 < JetThermalKernel.J v := by
  have hn : JetThermalKernel.J v ≠ 0 := by
    change v ∈ Function.support JetThermalKernel.J
    rw [JetThermalKernel.J_support]
    simpa only [mem_ball,dist_zero_right] using hv
  exact lt_of_le_of_ne (JetThermalKernel.J_nonneg v) hn.symm

theorem raw_pos {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ)
    {p : JetPrototype.Phase} (hx : ‖p.1‖ < δ/4) (hv : ‖p.2‖ < 1/2) : 0 < raw q δ p := by
  have hc : centeredSpace p.1 = p.1 := centeredSpace_eq (by linarith)
  have hu : ‖p.1.1‖ < δ/4 := (norm_fst_le p.1).trans_lt hx
  have hz : |p.1.2| < δ/4 := by simpa only [Real.norm_eq_abs] using (norm_snd_le p.1).trans_lt hx
  have hj : ‖PlaneChart.join p.1.1 p.1.2‖ < δ := by
    have he := PlaneChart.norm_join_sq p.1.1 p.1.2
    have hsq := sq_abs p.1.2
    nlinarith [norm_nonneg p.1.1,norm_nonneg (PlaneChart.join p.1.1 p.1.2),abs_nonneg p.1.2]
  have harg : ‖δ⁻¹ • PlaneChart.join p.1.1 p.1.2‖ < 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hδ)]
    exact (inv_mul_lt_one₀ hδ).mpr hj
  unfold raw
  rw [hc]
  exact mul_pos (J_pos harg) (div_pos (J_pos (by linarith)) (H_pos q p.2))

theorem raw_size_pos {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ) :
    0 < PhaseEssSup.size (raw q δ) := by
  let s : Set JetPrototype.Phase := ball (0 : Space) (δ/4) ×ˢ ball (0 : Velocity) (1/2)
  have hs : FlightMeasure.phaseVolume s ≠ 0 := by
    change ((volume : Measure Space).prod (volume : Measure Velocity))
      (ball (0 : Space) (δ/4) ×ˢ ball (0 : Velocity) (1/2)) ≠ 0
    rw [Measure.prod_prod]
    exact mul_ne_zero (measure_ball_pos volume (0 : Space) (by linarith)).ne'
      (measure_ball_pos volume (0 : Velocity) (by norm_num : (0:ℝ) < 1/2)).ne'
  apply PhaseEssSup.size_pos_of_positive_set (measurable_raw q δ)
    (fun p => by rw [abs_of_nonneg (raw_nonneg q δ p)]; exact raw_le q δ p) hs
  intro p hp
  exact raw_pos hδ hδmax q (by simpa only [mem_ball,dist_zero_right] using hp.1)
    (by simpa only [mem_ball,dist_zero_right] using hp.2)

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # The normalized periodic hot seed has the data required by cap selection -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem normalized_measurable (q δ : ℝ) : Measurable (normalized q δ) :=
  (measurable_raw q δ).const_mul _

theorem normalized_periodic (q δ : ℝ) (n : JetLattice.Lattice) (p : JetPrototype.Phase) :
    normalized q δ (WeightedTranslation.shift (JetCopyDatum.displacement n) p) = normalized q δ p := by
  unfold normalized
  rw [raw_periodic]

theorem normalized_bounds {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ p, 0 ≤ normalized q δ p ∧ normalized q δ p ≤ M := by
  have hs := raw_size_pos hδ hδmax q
  let c := δ/PhaseEssSup.size (raw q δ)
  have hc : 0 < c := div_pos hδ hs
  refine ⟨c*bound,mul_pos hc bound_pos,?_⟩
  intro p
  exact ⟨mul_nonneg hc.le (raw_nonneg q δ p),mul_le_mul_of_nonneg_left (raw_le q δ p) hc.le⟩

theorem normalized_norm {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ) :
    PhaseEssSup.size (normalized q δ) = δ :=
  normalized_size hδ.le (raw_size_pos hδ hδmax q)

theorem normalized_velocity_support {q δ : ℝ} {p : JetPrototype.Phase}
    (hp : normalized q δ p ≠ 0) : ‖p.2‖ < 1 := by
  apply lt_of_not_ge
  intro hv
  apply hp
  simp only [normalized,raw,JetThermalKernel.J_zero hv,zero_div,mul_zero]

theorem normalized_data {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ) :
    Measurable (normalized q δ) ∧
      (∃ M : ℝ, 0 < M ∧ ∀ p, 0 ≤ normalized q δ p ∧ normalized q δ p ≤ M) ∧
      (∀ n p, normalized q δ (WeightedTranslation.shift (JetCopyDatum.displacement n) p) = normalized q δ p) ∧
      PhaseEssSup.size (normalized q δ) = δ :=
  ⟨normalized_measurable q δ,normalized_bounds hδ hδmax q,normalized_periodic q δ,normalized_norm hδ hδmax q⟩

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # Scale-independent amplitude bound for the localized thermal seed -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Metric
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem J_eq_bound {v : Velocity} (hv : ‖v‖ ≤ 1/2) :
    JetThermalKernel.J v = JetThermalKernel.bound := by
  unfold JetThermalKernel.J ContDiffBump.normed JetThermalKernel.bound
  rw [JetThermalKernel.bump.one_of_mem_closedBall (by
    simpa only [mem_closedBall,dist_zero_right,JetThermalKernel.bump] using hv),one_div]

def velocityCore : Set Velocity := {v | ‖v‖ < 1/2 ∧ 1/8 < ‖transverse v‖}

theorem velocityCore_open : IsOpen velocityCore := by
  have hc : Continuous transverse := by
    unfold transverse
    fun_prop
  exact (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const hc.norm)

theorem velocityCore_nonempty : velocityCore.Nonempty := by
  let u : Transverse := PiLp.single 2 (0 : Fin 2) (1/4 : ℝ)
  have hu : ‖u‖ = 1/4 := by simp [u]
  have hj : ‖PlaneChart.join u 0‖ = 1/4 := by
    have h := PlaneChart.norm_join_sq u 0
    rw [hu] at h
    nlinarith [norm_nonneg (PlaneChart.join u 0)]
  refine ⟨PlaneChart.join u 0,?_⟩
  change ‖PlaneChart.join u 0‖ < 1/2 ∧ 1/8 < ‖transverse (PlaneChart.join u 0)‖
  rw [PlaneChart.transverse_join,hu,hj]
  norm_num

def velocityBound (q : ℝ) : ℝ := 1+(1/8 : ℝ)^(-q)

theorem velocityBound_pos (q : ℝ) : 0 < velocityBound q := by
  unfold velocityBound
  positivity

theorem H_le_velocityBound {q : ℝ} (hq : 0 ≤ q) {v : Velocity}
    (hv : v ∈ velocityCore) : H q v ≤ velocityBound q := by
  have he : Real.exp (-‖v‖^2) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  have hp : (1+‖v‖^2)^(-50 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖v‖]) (by norm_num)
  have hr : ‖transverse v‖^(-q) ≤ (1/8 : ℝ)^(-q) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hv.2.le (neg_nonpos.mpr hq)
  unfold H singularity velocityBound
  have hm : Real.exp (-‖v‖^2)*(1+‖v‖^2)^(-50 : ℝ) ≤ 1 := by
    simpa using mul_le_mul he hp (Real.rpow_nonneg (by positivity) _) (by norm_num : (0:ℝ) ≤ 1)
  exact (mul_le_mul_of_nonneg_right hm (by positivity)).trans (by linarith)

def normLower (q : ℝ) : ℝ := JetThermalKernel.bound^2/velocityBound q

theorem normLower_pos (q : ℝ) : 0 < normLower q :=
  div_pos (sq_pos_of_pos JetThermalKernel.bound_pos) (velocityBound_pos q)

theorem spatial_core {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) {x : Space}
    (hx : ‖x‖ < δ/8) :
    JetThermalKernel.J (δ⁻¹ • PlaneChart.join (centeredSpace x).1 (centeredSpace x).2) =
      JetThermalKernel.bound := by
  have hc : centeredSpace x = x := centeredSpace_eq (by linarith)
  rw [hc]
  apply J_eq_bound
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hδ)]
  apply (inv_mul_le_iff₀ hδ).mpr
  have hu : ‖x.1‖ < δ/8 := (norm_fst_le x).trans_lt hx
  have hz : |x.2| < δ/8 := by simpa only [Real.norm_eq_abs] using (norm_snd_le x).trans_lt hx
  have he := PlaneChart.norm_join_sq x.1 x.2
  nlinarith [norm_nonneg x.1,norm_nonneg (PlaneChart.join x.1 x.2),sq_abs x.2,abs_nonneg x.2]

theorem raw_ge_normLower {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    {p : JetPrototype.Phase} (hx : ‖p.1‖ < δ/8) (hv : p.2 ∈ velocityCore) :
    normLower q ≤ raw q δ p := by
  unfold raw
  rw [spatial_core hδ hδmax hx,J_eq_bound hv.1.le]
  unfold normLower
  rw [sq, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left JetThermalKernel.bound_pos.le (H_pos q p.2)
      (H_le_velocityBound hq hv)) JetThermalKernel.bound_pos.le

theorem normLower_le_size {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    normLower q ≤ PhaseEssSup.size (raw q δ) := by
  let s : Set JetPrototype.Phase := ball (0 : Space) (δ/8) ×ˢ velocityCore
  have hs : FlightMeasure.phaseVolume s ≠ 0 := by
    change ((volume : Measure Space).prod (volume : Measure Velocity))
      (ball (0 : Space) (δ/8) ×ˢ velocityCore) ≠ 0
    rw [Measure.prod_prod]
    exact mul_ne_zero (measure_ball_pos volume (0 : Space) (by linarith)).ne'
      (velocityCore_open.measure_ne_zero volume velocityCore_nonempty)
  obtain ⟨p,hp,hbound⟩ := exists_mem_of_measure_ne_zero_of_ae hs
    (ae_restrict_of_ae (PhaseEssSup.ae_abs_le_size (measurable_raw q δ)
      (fun p => by rw [abs_of_nonneg (raw_nonneg q δ p)]; exact raw_le q δ p)))
  exact (raw_ge_normLower hq hδ hδmax
    (by simpa only [mem_ball,dist_zero_right] using hp.1) hp.2).trans
      ((le_abs_self _).trans hbound)

theorem normalized_uniform_bound {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    (p : JetPrototype.Phase) :
    normalized q δ p ≤ (bound/normLower q)*δ := by
  have hs := normLower_le_size hq hδ hδmax
  have hn := normLower_pos q
  have hsize := hn.trans_le hs
  unfold normalized
  calc
    _ ≤ (δ/normLower q)*bound := mul_le_mul
      (div_le_div_of_nonneg_left hδ.le hn hs) (raw_le q δ p) (raw_nonneg q δ p)
      (div_nonneg hδ.le hn.le)
    _ = _ := by ring

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # Vanishing of the actual hot seed on the spatial torus -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotSeedProfile

def periodicDensity (q δ : ℝ) : Density :=
  fun p => JetPeriodicDatum.pullback (normalized q δ) p * H q p.2

theorem periodicDensity_measurable (q δ : ℝ) : Measurable (periodicDensity q δ) :=
  ((normalized_measurable q δ).comp
    (JetPeriodicDatum.phaseMap_measurePreserving.measurable.comp
      TorusChart.phase_measurePreserving.measurable)).mul
    ((ChartKernel.measurable_H q).comp measurable_snd)

theorem periodicDensity_nonneg {q δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (p : Phase) :
    0 ≤ periodicDensity q δ p := by
  obtain ⟨M,hM,hb⟩ := normalized_bounds hδ hδmax q
  exact mul_nonneg (hb _).1 (H_nonneg q p.2)

theorem periodicDensity_bound {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    (p : Phase) : periodicDensity q δ p ≤ (bound/normLower q)*δ*H q p.2 :=
  mul_le_mul_of_nonneg_right (normalized_uniform_bound hq hδ hδmax _) (H_nonneg _ _)

theorem integrable_weight_torus {q : ℝ} (hq : q < 2) :
    Integrable (fun p : Phase => H q p.2) := by
  rw [Measure.volume_eq_prod]
  simpa only [one_mul] using
    (integrable_const (1 : ℝ) : Integrable (fun _ : Position => (1 : ℝ))).mul_prod (integrable_H hq)

theorem periodicDensity_integrable {q δ : ℝ} (hq : 0 ≤ q) (hqmax : q < 2)
    (hδ : 0 < δ) (hδmax : δ ≤ 1) : Integrable (periodicDensity q δ) := by
  apply ((integrable_weight_torus hqmax).const_mul ((bound/normLower q)*δ)).mono'
    (periodicDensity_measurable q δ).aestronglyMeasurable
  exact ae_of_all _ (fun p => by
    rw [Real.norm_of_nonneg (periodicDensity_nonneg hδ hδmax p)]
    exact periodicDensity_bound hq hδ hδmax p)

theorem periodicDensity_support {q δ : ℝ} {p : Phase}
    (hp : periodicDensity q δ p ≠ 0) : ‖p.2‖ < 1 := by
  have hn : normalized q δ (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative p)) ≠ 0 :=
    left_ne_zero_of_mul hp
  exact normalized_velocity_support (q := q) (δ := δ)
    (p := JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative p)) hn

/-- Every allowed bounded cap-shot parameter gives the same vanishing hot perturbation. -/
theorem periodicDensity_L1_tendsto {q : ℝ} (hq : 0 ≤ q) (hqmax : q < 2)
    {δ ell : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδmax : ∀ n, δ n ≤ 1)
    (hδlim : Tendsto δ atTop (𝓝 0)) (hell : ∀ n, ell n ∈ Set.Icc (0:ℝ) 2) :
    Tendsto (fun n => ∫ p : Phase, ‖ell n*periodicDensity q (δ n) p‖) atTop (𝓝 0) := by
  let C := bound/normLower q
  have hC : 0 ≤ C := div_nonneg bound_pos.le (normLower_pos q).le
  have hbound (n : ℕ) (p : Phase) :
      ‖ell n*periodicDensity q (δ n) p‖ ≤ (2*C)*δ n*H q p.2 := by
    rw [Real.norm_of_nonneg (mul_nonneg (hell n).1 (periodicDensity_nonneg (hδ n) (hδmax n) p))]
    calc
      _ ≤ 2*((C*δ n)*H q p.2) := mul_le_mul (hell n).2
        (periodicDensity_bound hq (hδ n) (hδmax n) p)
        (periodicDensity_nonneg (hδ n) (hδmax n) p) (by norm_num)
      _ = _ := by ring
  have hmajor (n : ℕ) : ∀ᵐ p : Phase,
      ‖‖ell n*periodicDensity q (δ n) p‖‖ ≤ (2*C)*H q p.2 := by
    filter_upwards [] with p
    rw [norm_norm]
    exact (hbound n p).trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (mul_nonneg (by norm_num) hC) (hδmax n)) (H_nonneg _ _))
  have hlim : ∀ᵐ p : Phase,
      Tendsto (fun n => ‖ell n*periodicDensity q (δ n) p‖) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [] with p
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => hbound n p)
    simpa only [mul_zero,zero_mul] using (hδlim.const_mul (2*C)).mul_const (H q p.2)
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun p : Phase => (2*C)*H q p.2)
    (fun n => ((periodicDensity_measurable q (δ n)).const_mul (ell n)).aestronglyMeasurable.norm)
    ((integrable_weight_torus hqmax).const_mul (2*C)) hmajor hlim

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # Uniform scalar majorant after separating the escaped cold tail -/

namespace BoltzmannNonuniqueness.HotScalarBound

theorem remainder_majorant {M C z e s δ t : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hz : 0 ≤ z) (he : 0 ≤ e) (he₁ : e ≤ 1)
    (hδ : 0 < δ) (hδs : δ ≤ s) (ht : 0 < t) (ht₁ : t ≤ 1) :
    2*(z+e)*M/(s+t)+(z+e)^2*C ≤
      (2*M/(δ+t))*z+2*C*z^2+(2*M+2*C)*(e/t) := by
  have hst : 0 < s+t := by linarith
  have hδt : 0 < δ+t := by positivity
  have hzpart : (2*M*z)/(s+t) ≤ (2*M*z)/(δ+t) :=
    div_le_div_of_nonneg_left (by positivity) hδt (by linarith)
  have hepart : (2*M*e)/(s+t) ≤ (2*M*e)/t :=
    div_le_div_of_nonneg_left (by positivity) ht (by linarith)
  have hlinear : 2*(z+e)*M/(s+t) ≤ (2*M/(δ+t))*z+(2*M)*(e/t) := by
    calc
      _ = (2*M*z)/(s+t)+(2*M*e)/(s+t) := by ring
      _ ≤ (2*M*z)/(δ+t)+(2*M*e)/t := add_le_add hzpart hepart
      _ = _ := by ring
  have het : e ≤ e/t := (le_div_iff₀ ht).mpr (by nlinarith)
  have hsquare : (z+e)^2 ≤ 2*z^2+2*e := by
    nlinarith [sq_nonneg (z-e),mul_nonneg he (sub_nonneg.mpr he₁)]
  have hquad : (z+e)^2*C ≤ 2*C*z^2+2*C*(e/t) := by
    have h₁ := mul_le_mul_of_nonneg_right hsquare hC
    have h₂ := mul_le_mul_of_nonneg_left het (show 0 ≤ 2*C by positivity)
    nlinarith only [h₁,h₂]
  calc
    _ ≤ ((2*M/(δ+t))*z+(2*M)*(e/t))+(2*C*z^2+2*C*(e/t)) := add_le_add hlinear hquad
    _ = _ := by ring

end BoltzmannNonuniqueness.HotScalarBound


end

section

/-! # A uniform positive lower bound on the central core of the normalized hot seed -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem normalized_core_lower {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    {p : JetPrototype.Phase} (hx : ‖p.1‖ < δ/8) (hv : p.2 ∈ velocityCore) :
    δ*(normLower q/bound) ≤ normalized q δ p := by
  have hs : PhaseEssSup.size (raw q δ) ≤ bound :=
    PhaseEssSup.size_le bound_pos.le (measurable_raw q δ)
      (fun p => by rw [abs_of_nonneg (raw_nonneg q δ p)]; exact raw_le q δ p)
  have hpos := raw_size_pos hδ hδmax q
  unfold normalized
  calc
    δ*(normLower q/bound) = (δ/bound)*normLower q := by ring
    _ ≤ (δ/PhaseEssSup.size (raw q δ))*raw q δ p :=
      mul_le_mul (div_le_div_of_nonneg_left hδ.le hpos hs)
        (raw_ge_normLower hq hδ hδmax hx hv) (normLower_pos q).le (by positivity)

end BoltzmannNonuniqueness.HotSeedProfile

end

end

end OAI
