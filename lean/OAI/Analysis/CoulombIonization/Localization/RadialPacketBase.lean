import Mathlib
import OAI.Analysis.CoulombIonization.Variational.DiffuseSeed

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
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

def radialPacketBase (x : Space) : ℂ :=
  (Real.smoothTransition (1 - ‖x‖^2) : ℝ)

lemma radialPacketBase_smooth : ContDiff ℝ ∞ radialPacketBase := by
  apply Complex.ofRealCLM.contDiff.comp
  apply Real.smoothTransition.contDiff.comp
  exact contDiff_const.sub (contDiff_id.norm_sq ℝ)

lemma radialPacketBase_zero {x : Space} (hx : 1 ≤ ‖x‖) : radialPacketBase x = 0 := by
  have hh : 1 - ‖x‖^2 ≤ 0 := by nlinarith [norm_nonneg x]
  simp only [radialPacketBase, Real.smoothTransition.zero_of_nonpos hh,Complex.ofReal_zero]

lemma radialPacketBase_compact : HasCompactSupport radialPacketBase := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1)
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  by_contra hh
  exact hx (radialPacketBase_zero (not_le.mp hh).le)

lemma radialPacketBase_zero_value : radialPacketBase 0 = 1 := by
  simp [radialPacketBase,Real.smoothTransition.one_of_one_le]

def radialPacketSeed (x : Configuration 1) : ℂ := radialPacketBase (x 0)

lemma radialPacketSeed_smooth : ContDiff ℝ ∞ radialPacketSeed :=
  radialPacketBase_smooth.comp (ContinuousLinearMap.proj (0 : Fin 1) : Configuration 1 →L[ℝ] Space).contDiff

lemma radialPacketSeed_compact : HasCompactSupport radialPacketSeed := by
  exact radialPacketBase_compact.comp_homeomorph (Homeomorph.funUnique (Fin 1) Space)

lemma radialPacketSeed_radial {x y : Configuration 1} (h : ‖x 0‖ = ‖y 0‖) :
    radialPacketSeed x = radialPacketSeed y := by simp only [radialPacketSeed,radialPacketBase,h]

lemma radialPacketSeed_support {x : Configuration 1} (hx : radialPacketSeed x ≠ 0) :
    ‖x 0‖ < 1 := by
  by_contra hh
  exact hx (radialPacketBase_zero (not_lt.mp hh))

lemma radialPacketSeed_mass_pos : 0 < formMass (smoothForm radialPacketSeed) := by
  have hi : 0 < ∫ x, ‖radialPacketSeed x‖^2 :=
    (radialPacketSeed_smooth.continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (compact_norm_sq radialPacketSeed_compact) (fun x => sq_nonneg _)
      (x := 0) (by simp [radialPacketSeed,radialPacketBase_zero_value])
  change 0 < ∑ _s : Spins 1, ∫ x, ‖radialPacketSeed x‖^2
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hi

def radialScaledSeed (R : ℝ) (x : Configuration 1) : ℂ := radialPacketSeed (R⁻¹ • x)

def radialScaledRaw (R : ℝ) : FormVector 1 := smoothForm (radialScaledSeed R)

lemma radialScaledSeed_smooth (R : ℝ) : ContDiff ℝ ∞ (radialScaledSeed R) :=
  radialPacketSeed_smooth.comp (R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1)).contDiff

lemma radialScaledSeed_compact {R : ℝ} (hR : 0 < R) : HasCompactSupport (radialScaledSeed R) :=
  radialPacketSeed_compact.comp_smul (inv_ne_zero hR.ne')

lemma radialScaledRaw_sobolev (R : ℝ) (hR : 0 < R) : SobolevFermion (radialScaledRaw R) := by
  refine ⟨fun _ => (radialScaledSeed_smooth R).continuous.memLp_of_hasCompactSupport
    (radialScaledSeed_compact hR),fun s i a => ?_,fun s i a φ hφ hcφ => ?_,?_⟩
  · exact (smooth_derivative_continuous (radialScaledSeed_smooth R) _).memLp_of_hasCompactSupport
      (compact_derivative (radialScaledSeed_compact hR) _)
  · exact smooth_weak_gradient (radialScaledSeed_smooth R) (radialScaledSeed_compact hR) hφ hcφ _
  · intro π s
    have hp : π = 1 := Subsingleton.elim _ _
    subst π
    exact Eventually.of_forall fun x => by simp [radialScaledRaw,smoothForm]

lemma radialScaledRaw_mass_pos {R : ℝ} (hR : 0 < R) : 0 < formMass (radialScaledRaw R) := by
  have hn : radialScaledSeed R 0 = 1 := by
    simp only [radialScaledSeed,smul_zero,radialPacketSeed,Pi.zero_apply,radialPacketBase_zero_value]
  have hi : 0 < ∫ x, ‖radialScaledSeed R x‖^2 :=
    ((radialScaledSeed_smooth R).continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (compact_norm_sq (radialScaledSeed_compact hR)) (fun x => sq_nonneg _)
      (x := 0) (by rw [hn]; norm_num)
  change 0 < ∑ _s : Spins 1, ∫ x, ‖radialScaledSeed R x‖^2
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hi

lemma radialScaledRaw_gradient (R : ℝ) (s : Spins 1) (i : Fin 1) (a : Fin 3) (x : Configuration 1) :
    (radialScaledRaw R).gradient s i a x = R⁻¹ •
      (smoothForm radialPacketSeed).gradient s i a (R⁻¹ • x) := by
  change fderiv ℝ (radialPacketSeed ∘ ⇑(R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1))) x (direction i a) = _
  rw [fderiv_comp x (radialPacketSeed_smooth.differentiable (by simp)).differentiableAt
    (R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.fderiv,
    smul_apply,ContinuousLinearMap.id_apply,map_smul,smoothForm]

lemma radialScaledRaw_mass (R : ℝ) (hR : 0 < R) :
    formMass (radialScaledRaw R) = R ^ Module.finrank ℝ (Configuration 1) *
      formMass (smoothForm radialPacketSeed) := by
  unfold formMass
  simp only [radialScaledRaw,smoothForm,radialScaledSeed]
  have hi := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Configuration 1))
    (fun x => ‖radialPacketSeed x‖^2) hR.le
  simp only [smul_eq_mul] at hi
  simp_rw [hi,Finset.mul_sum]

lemma radialScaledRaw_kinetic (R : ℝ) (hR : 0 < R) :
    formKinetic (radialScaledRaw R) = R⁻¹^2 * R ^ Module.finrank ℝ (Configuration 1) *
      formKinetic (smoothForm radialPacketSeed) := by
  unfold formKinetic
  simp_rw [radialScaledRaw_gradient,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
  have hi (s : Spins 1) (i : Fin 1) (a : Fin 3) :=
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Configuration 1))
      (fun x => ‖(smoothForm radialPacketSeed).gradient s i a x‖^2) hR.le
  simp only [smul_eq_mul] at hi
  simp_rw [hi,← Finset.mul_sum]
  ring

def radialScaledOrbital (R : ℝ) : FormVector 1 :=
  scaleForm (Real.sqrt (formMass (radialScaledRaw R)))⁻¹ (radialScaledRaw R)

lemma radialScaledOrbital_admissible {R : ℝ} (hR : 0 < R) : FormAdmissible (radialScaledOrbital R) :=
  (radialScaledRaw_sobolev R hR).normalize (radialScaledRaw_mass_pos hR)

def radialPacketKinetic : ℝ :=
  formKinetic (smoothForm radialPacketSeed) / formMass (smoothForm radialPacketSeed)

lemma radialPacketKinetic_nonneg : 0 ≤ radialPacketKinetic :=
  div_nonneg (formKinetic_nonneg _) (by unfold formMass; positivity)

lemma radialScaledOrbital_kinetic {R : ℝ} (hR : 0 < R) :
    formKinetic (radialScaledOrbital R) = radialPacketKinetic / R^2 := by
  have hmpos : 0 < formMass (smoothForm radialPacketSeed) := by
    have hh := radialScaledRaw_mass_pos (by norm_num : (0:ℝ)<1)
    rw [radialScaledRaw_mass 1 (by norm_num), one_pow, one_mul] at hh
    exact hh
  rw [radialScaledOrbital,formKinetic_scale,inv_pow,Real.sq_sqrt (radialScaledRaw_mass_pos hR).le,
    radialScaledRaw_mass R hR,radialScaledRaw_kinetic R hR,radialPacketKinetic]
  field_simp

def radialCenterShift (y : Space) : Configuration 1 :=
  fun _ => -y

def radialLocalSeed (y : Space) (R : ℝ) (x : Configuration 1) : ℂ :=
  radialScaledSeed R (x + radialCenterShift y)

def radialLocalRaw (y : Space) (R : ℝ) : FormVector 1 := smoothForm (radialLocalSeed y R)

lemma radialLocalSeed_smooth (y : Space) (R : ℝ) : ContDiff ℝ ∞ (radialLocalSeed y R) :=
  (radialScaledSeed_smooth R).comp (contDiff_id.add contDiff_const)

lemma radialLocalSeed_compact (y : Space) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (radialLocalSeed y R) :=
  (radialScaledSeed_compact hR).comp_homeomorph (Homeomorph.addRight (radialCenterShift y))

lemma radialLocalRaw_sobolev (y : Space) {R : ℝ} (hR : 0 < R) :
    SobolevFermion (radialLocalRaw y R) := by
  refine ⟨fun _ => (radialLocalSeed_smooth y R).continuous.memLp_of_hasCompactSupport
    (radialLocalSeed_compact y hR),fun s i a => ?_,fun s i a φ hφ hcφ => ?_,?_⟩
  · exact (smooth_derivative_continuous (radialLocalSeed_smooth y R) _).memLp_of_hasCompactSupport
      (compact_derivative (radialLocalSeed_compact y hR) _)
  · exact smooth_weak_gradient (radialLocalSeed_smooth y R) (radialLocalSeed_compact y hR) hφ hcφ _
  · intro π s
    have hp : π = 1 := Subsingleton.elim _ _
    subst π
    exact Eventually.of_forall fun x => by simp [radialLocalRaw,smoothForm]

lemma radialLocalRaw_gradient (y : Space) (R : ℝ) (s : Spins 1) (i : Fin 1) (a : Fin 3)
    (x : Configuration 1) :
    (radialLocalRaw y R).gradient s i a x = (radialScaledRaw R).gradient s i a (x+radialCenterShift y) := by
  change fderiv ℝ ((radialScaledSeed R) ∘ (fun z => z+radialCenterShift y)) x (direction i a) = _
  have ht : HasFDerivAt (fun z : Configuration 1 => z+radialCenterShift y)
      (ContinuousLinearMap.id ℝ (Configuration 1)) x := by
    simpa only [id_eq] using (hasFDerivAt_id (𝕜 := ℝ) x).add_const (radialCenterShift y)
  have hh := ((radialScaledSeed_smooth R).differentiable (by simp) (x+radialCenterShift y)).hasFDerivAt.comp x ht
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,radialScaledRaw,smoothForm]

lemma radialLocalRaw_mass (y : Space) (R : ℝ) :
    formMass (radialLocalRaw y R) = formMass (radialScaledRaw R) := by
  unfold formMass
  apply Finset.sum_congr rfl
  intro s _
  exact integral_add_right_eq_self (fun x => ‖(radialScaledRaw R).value s x‖^2) _

lemma radialLocalRaw_kinetic (y : Space) (R : ℝ) :
    formKinetic (radialLocalRaw y R) = formKinetic (radialScaledRaw R) := by
  unfold formKinetic
  simp_rw [radialLocalRaw_gradient]
  congr 1
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro a _
  exact integral_add_right_eq_self (μ := volume)
    (fun z : Configuration 1 => ‖(radialScaledRaw R).gradient s i a z‖^2) (radialCenterShift y)

def radialLocalOrbital (y : Space) (R : ℝ) : FormVector 1 :=
  scaleForm (Real.sqrt (formMass (radialLocalRaw y R)))⁻¹ (radialLocalRaw y R)

lemma radialLocalOrbital_admissible (y : Space) {R : ℝ} (hR : 0 < R) :
    FormAdmissible (radialLocalOrbital y R) := by
  apply (radialLocalRaw_sobolev y hR).normalize
  rw [radialLocalRaw_mass]
  exact radialScaledRaw_mass_pos hR

lemma radialLocalOrbital_kinetic (y : Space) {R : ℝ} (hR : 0 < R) :
    formKinetic (radialLocalOrbital y R) = radialPacketKinetic / R^2 := by
  calc
    _ = formKinetic (radialScaledOrbital R) := by
      rw [radialLocalOrbital,radialScaledOrbital,formKinetic_scale,formKinetic_scale,
        radialLocalRaw_mass,radialLocalRaw_kinetic]
    _ = _ := radialScaledOrbital_kinetic hR

lemma radialLocalSeed_support (y : Space) {R : ℝ} (hR : 0 < R) {x : Configuration 1}
    (hx : radialLocalSeed y R x ≠ 0) : ‖x 0-y‖ < R := by
  have hh := radialPacketSeed_support hx
  change ‖R⁻¹ • (x 0 + -y)‖ < 1 at hh
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),← div_eq_inv_mul] at hh
  simpa only [sub_eq_add_neg] using (div_lt_one hR).mp hh

lemma radialLocalRaw_zero (y : Space) {R : ℝ} (hR : 0 < R) {x : Configuration 1}
    (hx : R < ‖x 0-y‖) : FormZeroAt (radialLocalRaw y R) x := by
  have hz (z : Configuration 1) (hz : R < ‖z 0-y‖) : radialLocalSeed y R z = 0 := by
    by_contra hn
    exact (not_lt_of_ge (le_of_lt hz)) (radialLocalSeed_support y hR hn)
  have he : radialLocalSeed y R =ᶠ[𝓝 x] fun _ => (0:ℂ) :=
    ((((continuous_apply (0 : Fin 1)).sub continuous_const).norm.tendsto x).eventually
      (eventually_gt_nhds hx)).mono fun z hz' => hz z hz'
  intro s
  refine ⟨hz x hx,fun i a => ?_⟩
  change fderiv ℝ (radialLocalSeed y R) x (direction i a) = 0
  rw [he.fderiv_eq]
  simp

lemma radialLocalOrbital_zero (y : Space) {R : ℝ} (hR : 0 < R) {x : Configuration 1}
    (hx : R < ‖x 0-y‖) : FormZeroAt (radialLocalOrbital y R) x := by
  intro s
  have hh := radialLocalRaw_zero y hR hx s
  constructor
  · change _ * (radialLocalRaw y R).value s x = 0
    rw [hh.1,mul_zero]
  · intro i a
    change _ * (radialLocalRaw y R).gradient s i a x = 0
    rw [hh.2,mul_zero]

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
