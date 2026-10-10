import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.Radial

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
namespace CoulombAnalysis

lemma tfSpace_unitBall_volume : volume.real (ball (0 : TFSpace) 1) = 4 * Real.pi / 3 := by
  rw [Measure.real, InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by simp [TFSpace])]
  norm_num [Nat.doubleFactorial]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

lemma tfSpace_radial_integral (f : ℝ → ℝ) :
    ∫ x : TFSpace, f ‖x‖ = 4 * Real.pi * ∫ r in Ioi 0, r ^ 2 * f r := by
  rw [integral_fun_norm_addHaar volume f, tfSpace_unitBall_volume]
  simp only [TFSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma integral_Iic_hasDerivAt {f : ℝ → ℝ} (hf : Integrable f) {r : ℝ}
    (hc : ContinuousAt f r) : HasDerivAt (fun s => ∫ t in Iic s, f t) (f r) r := by
  have he : (fun s => ∫ t in Iic s, f t) =
      fun s => (∫ t in r..s, f t) + ∫ t in Iic r, f t := by
    funext s
    have hh := intervalIntegral.integral_Iic_sub_Iic (hf.integrableOn (s := Iic r))
      (hf.integrableOn (s := Iic s))
    linarith
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right hf.intervalIntegrable
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hc).add_const _

lemma integral_Ioi_hasDerivAt {f : ℝ → ℝ} (hf : Integrable f) {r : ℝ}
    (hc : ContinuousAt f r) : HasDerivAt (fun s => ∫ t in Ioi s, f t) (-f r) r := by
  have he : (fun s => ∫ t in Ioi s, f t) =
      fun s => (∫ t in Ioi r, f t) - ∫ t in r..s, f t := by
    funext s
    have hh := intervalIntegral.integral_Ioi_sub_Ioi' (hf.integrableOn (s := Ioi r))
      (hf.integrableOn (s := Ioi s))
    linarith
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right hf.intervalIntegrable
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hc).const_sub _

def radialAxis : TFSpace := EuclideanSpace.single 0 1

@[simp] lemma radialAxis_norm : ‖radialAxis‖ = 1 := by simp [radialAxis]

def radialTrace (ρ : TFSpace → ℝ) (r : ℝ) : ℝ := ρ (r • radialAxis)

lemma IsRadial.trace {ρ : TFSpace → ℝ} (hr : IsRadial ρ) (x : TFSpace) :
    ρ x = radialTrace ρ ‖x‖ := by
  exact hr x (‖x‖ • radialAxis) (by simp [norm_smul])

lemma radialTrace_continuousAt {ρ : TFSpace → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) : ContinuousAt (radialTrace ρ) r := by
  change ContinuousAt (fun s => ρ (s • radialAxis)) r
  have hg : ContinuousAt (fun s : ℝ => s • radialAxis) r := by fun_prop
  exact ContinuousAt.comp (f := fun s : ℝ => s • radialAxis) (hc (r • radialAxis) (smul_ne_zero hr.ne' (by
    apply norm_ne_zero_iff.mp; rw [radialAxis_norm]; norm_num))) hg

lemma radialTrace_mem2 {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hr : IsRadial ρ) :
    IntegrableOn (fun s : ℝ => s ^ 2 * radialTrace ρ s) (Ioi 0) := by
  have he : (fun x : TFSpace => radialTrace ρ ‖x‖) = ρ := funext fun x => (hr.trace x).symm
  have hi : Integrable (fun x : TFSpace => radialTrace ρ ‖x‖) := by rwa [he]
  have hh := (integrable_fun_norm_addHaar (volume : Measure TFSpace) (f := radialTrace ρ)).mp hi
  simpa only [TFSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul] using hh

lemma radialTrace_mem1 {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    (hr : IsRadial ρ) : IntegrableOn (fun s : ℝ => s * radialTrace ρ s) (Ioi 0) := by
  have hi := tfPotential_integrable h1 hp 0
  simp only [zero_sub, norm_neg] at hi
  have he : (fun x : TFSpace => radialTrace ρ ‖x‖ / ‖x‖) = (fun x => ρ x / ‖x‖) :=
    funext fun x => by rw [← hr.trace]
  have hh := (integrable_fun_norm_addHaar (volume : Measure TFSpace)
    (f := fun s => radialTrace ρ s / s)).mp (he ▸ hi)
  simp only [TFSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul] at hh
  apply hh.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hn : s ≠ 0 := ne_of_gt (show 0 < s from hs)
  field_simp [hn]

def radialMassIntegrand (ρ : TFSpace → ℝ) : ℝ → ℝ :=
  (Ioi 0).indicator (fun s => s ^ 2 * radialTrace ρ s)

def radialTailIntegrand (ρ : TFSpace → ℝ) : ℝ → ℝ :=
  (Ioi 0).indicator (fun s => s * radialTrace ρ s)

def radialMass (ρ : TFSpace → ℝ) (r : ℝ) : ℝ :=
  4 * Real.pi * ∫ s in Iic r, radialMassIntegrand ρ s

def radialTail (ρ : TFSpace → ℝ) (r : ℝ) : ℝ :=
  4 * Real.pi * ∫ s in Ioi r, radialTailIntegrand ρ s

lemma radialMassIntegrand_integrable {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hr : IsRadial ρ) :
    Integrable (radialMassIntegrand ρ) :=
  (radialTrace_mem2 h1 hr).integrable_indicator measurableSet_Ioi

lemma radialTailIntegrand_integrable {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ) : Integrable (radialTailIntegrand ρ) :=
  (radialTrace_mem1 h1 hp hr).integrable_indicator measurableSet_Ioi

lemma radialMassIntegrand_continuousAt {ρ : TFSpace → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) : ContinuousAt (radialMassIntegrand ρ) r := by
  have he : radialMassIntegrand ρ =ᶠ[𝓝 r] (fun s => s ^ 2 * radialTrace ρ s) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact indicator_of_mem hs _
  exact ((continuousAt_id.pow 2).mul (radialTrace_continuousAt hr hc)).congr he.symm

lemma radialTailIntegrand_continuousAt {ρ : TFSpace → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) : ContinuousAt (radialTailIntegrand ρ) r := by
  have he : radialTailIntegrand ρ =ᶠ[𝓝 r] (fun s => s * radialTrace ρ s) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact indicator_of_mem hs _
  exact (continuousAt_id.mul (radialTrace_continuousAt hr hc)).congr he.symm

lemma radialMass_hasDerivAt {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {r : ℝ} (hrp : 0 < r) :
    HasDerivAt (radialMass ρ) (4 * Real.pi * r ^ 2 * radialTrace ρ r) r := by
  have hh := (integral_Iic_hasDerivAt (radialMassIntegrand_integrable h1 hr)
    (radialMassIntegrand_continuousAt hrp hc)).const_mul (4 * Real.pi)
  unfold radialMass
  simpa [radialMassIntegrand, hrp, mul_assoc] using hh

lemma radialTail_hasDerivAt {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    (hr : IsRadial ρ) (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {r : ℝ} (hrp : 0 < r) :
    HasDerivAt (radialTail ρ) (-(4 * Real.pi * r * radialTrace ρ r)) r := by
  have hh := (integral_Ioi_hasDerivAt (radialTailIntegrand_integrable h1 hp hr)
    (radialTailIntegrand_continuousAt hrp hc)).const_mul (4 * Real.pi)
  unfold radialTail
  simpa [radialTailIntegrand, hrp, mul_assoc, mul_neg] using hh

lemma radialMass_contDiffOn {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) : ContDiffOn ℝ 1 (radialMass ρ) (Ioi 0) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun r hrp => (radialMass_hasDerivAt h1 hr hc hrp).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  have he : EqOn (deriv (radialMass ρ)) (fun r => 4 * Real.pi * r ^ 2 * radialTrace ρ r) (Ioi 0) :=
    fun r hrp => (radialMass_hasDerivAt h1 hr hc hrp).deriv
  apply ContinuousOn.congr _ (fun r hrp => he hrp)
  exact fun r hrp => ((continuousAt_const.mul (continuousAt_id.pow 2)).mul
    (radialTrace_continuousAt hrp hc)).continuousWithinAt

lemma radialMass_eq_integral {ρ : TFSpace → ℝ} (hr : IsRadial ρ) (r : ℝ) :
    radialMass ρ r = ∫ y in {y : TFSpace | ‖y‖ ≤ r}, ρ y := by
  have hm : MeasurableSet {y : TFSpace | ‖y‖ ≤ r} := measurableSet_le measurable_norm measurable_const
  have he : {y : TFSpace | ‖y‖ ≤ r}.indicator ρ =
      (fun y => (Iic r).indicator (radialTrace ρ) ‖y‖) := by
    funext y
    by_cases hy : ‖y‖ ≤ r <;> simp [hy, hr.trace y]
  rw [← integral_indicator hm, he, tfSpace_radial_integral]
  unfold radialMass
  congr 1
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae (Eventually.of_forall fun s => ?_)
  by_cases hs : 0 < s <;> by_cases hsr : s ≤ r <;> simp [radialMassIntegrand, hs, hsr]

lemma radialTail_eq_integral {ρ : TFSpace → ℝ} (hr : IsRadial ρ) (r : ℝ) :
    radialTail ρ r = ∫ y in {y : TFSpace | r < ‖y‖}, ρ y / ‖y‖ := by
  have hm : MeasurableSet {y : TFSpace | r < ‖y‖} := measurableSet_lt measurable_const measurable_norm
  have he : {y : TFSpace | r < ‖y‖}.indicator (fun y => ρ y / ‖y‖) =
      (fun y => (Ioi r).indicator (fun s => radialTrace ρ s / s) ‖y‖) := by
    funext y
    by_cases hy : r < ‖y‖ <;> simp [hy, hr.trace y]
  rw [← integral_indicator hm, he, tfSpace_radial_integral]
  unfold radialTail
  congr 1
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae (Eventually.of_forall fun s => ?_)
  by_cases hs : 0 < s <;> by_cases hsr : r < s <;> simp [radialTailIntegrand, hs, hsr]
  field_simp [hs.ne']

def radialPotential (ρ : TFSpace → ℝ) (r : ℝ) : ℝ := radialMass ρ r / r + radialTail ρ r

lemma tfPotential_eq_radialPotential {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) {x : TFSpace} (hx : x ≠ 0) :
    tfPotential ρ x = radialPotential ρ ‖x‖ := by
  rw [tfPotential_newton h1 hp hr hR hs hx, radialPotential,
    radialMass_eq_integral hr, radialTail_eq_integral hr]

lemma radialPotential_hasDerivAt {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {r : ℝ} (hrp : 0 < r) :
    HasDerivAt (radialPotential ρ) (-(radialMass ρ r) / r ^ 2) r := by
  have hh := ((radialMass_hasDerivAt h1 hr hc hrp).div (hasDerivAt_id r) hrp.ne').add
    (radialTail_hasDerivAt h1 hp hr hc hrp)
  simp only [id_eq] at hh
  convert hh using 1 <;> (try rfl)
  field_simp [hrp.ne']
  ring

lemma radialPotential_contDiffOn {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) : ContDiffOn ℝ 2 (radialPotential ρ) (Ioi 0) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun r hrp => (radialPotential_hasDerivAt h1 hp hr hc hrp).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  have he : EqOn (deriv (radialPotential ρ)) (fun r => -(radialMass ρ r) / r ^ 2) (Ioi 0) :=
    fun r hrp => (radialPotential_hasDerivAt h1 hp hr hc hrp).deriv
  apply ContDiffOn.congr _ (fun r hrp => he hrp)
  exact (radialMass_contDiffOn h1 hr hc).neg.div (contDiffOn_id.pow 2)
    (fun r hrp => pow_ne_zero _ (ne_of_gt hrp))

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology

end

end OAI
