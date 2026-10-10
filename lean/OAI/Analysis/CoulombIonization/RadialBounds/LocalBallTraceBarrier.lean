import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.LocalOrdinaryBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma ballIndicator_measurable (y : Space) (R : ℝ) :
    Measurable (fun z : Space => if ‖z-y‖ < R then (1:ℝ) else 0) :=
  measurable_const.ite ((isOpen_lt ((continuous_id.sub continuous_const).norm)
    continuous_const).measurableSet) measurable_const

lemma weightedParticleCount_ball {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) (R : ℝ) :
    weightedParticleCount ψ (fun z => if ‖z-y‖ < R then 1 else 0) =
      rawFormPair ψ (rawBallCount y R) := by
  have hB (z : Space) : ‖if ‖z-y‖ < R then (1:ℝ) else 0‖ ≤ 1 := by split_ifs <;> norm_num
  unfold weightedParticleCount rawFormPair rawBallCount
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [Finset.sum_mul]
  exact (integral_finsetSum _ (fun i _ =>
    weightedParticleCount_integrable hψ (ballIndicator_measurable y R) hB s i)).symm

lemma weightedParticleCount_le_ball {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    {w : Space → ℝ} (hw : Measurable w) {B : ℝ} (hB : ∀ z, ‖w z‖ ≤ B)
    (y : Space) (R : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hle : ∀ z, w z ≤ C*(if ‖z-y‖ < R then 1 else 0)) :
    weightedParticleCount ψ w ≤ C*Real.sqrt (rawCountMoment ψ y R)*Real.sqrt (formMass ψ) := by
  have hi (z : Space) : ‖C*(if ‖z-y‖ < R then (1:ℝ) else 0)‖ ≤ C := by
    split_ifs <;> simp [hC,Real.norm_of_nonneg hC]
  have hh := weightedParticleCount_mono
    (fun s i => weightedParticleCount_integrable hψ hw hB s i)
    (fun s i => weightedParticleCount_integrable hψ
      (measurable_const.mul (ballIndicator_measurable y R)) hi s i) hle
  change weightedParticleCount ψ w ≤ weightedParticleCount ψ (fun z => C * (if ‖z-y‖ < R then 1 else 0)) at hh
  rw [weightedParticleCount_const_mul,weightedParticleCount_ball hψ] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (rawBallFirst_le_sqrt_count hψ y R) hC).trans_eq (by ring))

lemma radialInside_sq_count {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b R : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b ≤ R) :
    weightedParticleCount ψ (fun z => (radialInside y ht hb).value z^2) ≤
      Real.sqrt (rawCountMoment ψ y R)*Real.sqrt (formMass ψ) := by
  have hq (z : Space) : |(radialInside y ht hb).value z| ≤ 1 := Real.abs_cos_le_one _
  have hq2 (z : Space) : (radialInside y ht hb).value z^2 ≤ 1 := by
    nlinarith [hq z,abs_nonneg ((radialInside y ht hb).value z),sq_abs ((radialInside y ht hb).value z)]
  have hB (z : Space) : ‖(radialInside y ht hb).value z^2‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hq2 z
  have he (z : Space) : (radialInside y ht hb).value z^2 ≤ 1*(if ‖z-y‖ < R then 1 else 0) := by
    split_ifs with hz
    · simpa only [mul_one] using hq2 z
    · have hn : t+b ≤ ‖z-y‖ := hR.trans (le_of_not_gt hz)
      simp only [radialInside,radialPhase_pi_half ht hb hn,Real.cos_pi_div_two,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
  simpa only [one_mul, Pi.pow_apply] using weightedParticleCount_le_ball hψ
    (w := fun z => (radialInside y ht hb).value z^2)
    (by exact ((radialInside y ht hb).regular.continuous.pow 2).measurable) hB y R (by norm_num : (0:ℝ) ≤ 1) he

lemma radialInside_derivative_count {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b R : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b < R) (a : Fin 3) :
    weightedParticleCount ψ (fun z => (lineDeriv ℝ (radialInside y ht hb).value z (spaceDirections a))^2) ≤
      (Real.pi*smoothTransitionBound/b)^2*Real.sqrt (rawCountMoment ψ y R)*Real.sqrt (formMass ψ) := by
  let q := radialInside y ht hb
  have hd (z : Space) : |lineDeriv ℝ q.value z (spaceDirections a)| ≤ Real.pi*smoothTransitionBound/b := by
    dsimp only [q,radialInside]
    rw [radial_cos_derivative,abs_mul,abs_neg]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
      (by simpa only [one_mul] using radialPhase_derivative_le y ht hb z a)
  have hC : 0 ≤ Real.pi*smoothTransitionBound/b := by have := smoothTransitionBound_pos; positivity
  have hd2 (z : Space) : (lineDeriv ℝ q.value z (spaceDirections a))^2 ≤ (Real.pi*smoothTransitionBound/b)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hd z) 2
  have hB (z : Space) : ‖(lineDeriv ℝ q.value z (spaceDirections a))^2‖ ≤ (Real.pi*smoothTransitionBound/b)^2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hd2 z
  apply weightedParticleCount_le_ball hψ ((q.derivative_continuous a).pow 2).measurable hB y R (sq_nonneg _)
  intro z
  simp only [Pi.pow_apply]
  split_ifs with hz
  · simpa only [mul_one] using hd2 z
  · have hoff : ¬ (t ≤ ‖z-y‖ ∧ ‖z-y‖ ≤ t+b) := fun hh => hz (lt_of_le_of_lt hh.2 hR)
    dsimp only [q,radialInside]
    rw [radial_cos_derivative,radialPhase_derivative_zero_off_collar ht hb hoff,mul_zero]
    norm_num

lemma radialInside_density_error {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b R : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b < R) :
    densityLocalizationError ψ (radialInside y ht hb) ≤
      3*(Real.pi*smoothTransitionBound/b)^2*Real.sqrt (rawCountMoment ψ y R)*Real.sqrt (formMass ψ) := by
  have hh := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
    radialInside_derivative_count hψ y ht hb hR a)
  simpa only [densityLocalizationError,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using hh

open MeasureTheory Filter Set Metric
open scoped BigOperators

def sharpOrdinaryDensityConstant : ℝ :=
  32*actualCellMomentConstant+(4096/3:ℝ)*(2*sharpFreshKineticConstant+
    3*(Real.pi*smoothTransitionBound)^2*actualCellMomentConstant)

lemma radialInside_nonzero_lt {y z : Space} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hz : (radialInside y ht hb).value z ≠ 0) : ‖z-y‖ < t+b := by
  by_contra hn
  apply hz
  change Real.cos (radialPhase y t b z) = 0
  rw [radialPhase_pi_half ht hb (le_of_not_gt hn),Real.cos_pi_div_two]

 theorem sharp_cell_ordinary_density {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {y : Space} (hy : y ≠ 0)
    (ha1 : localCellRadius y ≤ 1) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (∫ z in ball y (4*localCellRadius y), (ordinaryDensity ψ z)^(5/3:ℝ)) ≤
      sharpOrdinaryDensityConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)^2/localCellRadius y := by
  let a := localCellRadius y
  let m := localOffsetMass (max (corePriceExcess Z lam ψ) 0) y
  let C := actualCellMomentConstant
  have ha : 0 < a := localCellRadius_pos hy
  have hm1 : 1 ≤ m := localOffsetMass_one_le _ _
  have hm0 : 0 ≤ m := le_trans zero_le_one hm1
  have ham : 1 ≤ a*m := cell_mass_product ha hm1 (localOffsetMass_cube_le _ _)
  have hc : a ≤ a^2*m := by nlinarith [mul_le_mul_of_nonneg_left ham ha.le]
  have hm : formMass ψ = 1 := hψ.2.2.2.2.1
  have hsv := hψ.sobolevFermion.sobolevVector
  obtain ⟨hr,hT⟩ := sharp_cell_fresh_kinetic hψ.sobolevFermion hm hy ha le_rfl
    (show 5*a ∈ Icc (5*localCellRadius y) (6*localCellRadius y) by constructor <;> dsimp only [a] at * <;> linarith)
    hZ hlam hc
  let q := radialInside y (show 0 ≤ 4*a by positivity) ha
  have hq (z : Space) : |q.value z| ≤ 1 := Real.abs_cos_le_one _
  have hout (z : Space) (hz : q.value z ≠ 0) : z ∉ radialPatchCore y (5*a) := by
    have hh := radialInside_nonzero_lt (show 0 ≤ 4*a by positivity) ha hz
    change ¬ (5*a ≤ ‖z-y‖)
    linarith
  have hg := localGradientTrace_le_full_out hsv (coreFirstRadialCut y hr ha)
    (coreFirstRadialCut_partition y hr ha) q hq
    (fun z hz => coreFirstRadialCut_core_zero y hr ha z (hout z hz))
    (fun z hz i => coreFirstRadialCut_core_deriv_zero y hr ha z (hout z hz) i)
  have hg' : localGradientTrace ψ q ≤ 2*sharpFreshKineticConstant*(m^2/a) :=
    (hg.trans (mul_le_mul_of_nonneg_left hT (by norm_num))).trans_eq (by ring)
  have hcount := priced_enlarged_cell_count hψ.sobolevFermion hm hZ hlam hy
  have hroot : Real.sqrt (rawCountMoment ψ y (32*a)) ≤ C*m := by
    simpa using sqrt_count_scale (rawCountMoment_nonneg ψ y (32*a)) actualCellMomentConstant_one_le
      (by norm_num : (0:ℝ) ≤ 1) hm0 (by simpa using hcount)
  have hn := radialInside_sq_count hsv y (show 0 ≤ 4*a by positivity) ha
    (show 4*a+a ≤ 32*a by linarith)
  have he := radialInside_density_error hsv y (show 0 ≤ 4*a by positivity) ha
    (show 4*a+a < 32*a by linarith)
  rw [hm,Real.sqrt_one,mul_one] at hn he
  have hmle : m ≤ m^2/a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left ha1 hm0]
  have hma : m/a^2 ≤ m^2/a := by
    apply (div_le_div_iff₀ (sq_pos_of_pos ha) ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left ham (mul_nonneg ha.le hm0)]
  have hC0 : 0 ≤ C := le_trans zero_le_one actualCellMomentConstant_one_le
  have hn' : weightedParticleCount ψ (fun z => q.value z^2) ≤ C*(m^2/a) :=
    hn.trans (hroot.trans (mul_le_mul_of_nonneg_left hmle hC0))
  have he' : densityLocalizationError ψ q ≤ 3*(Real.pi*smoothTransitionBound)^2*C*(m^2/a) := by
    calc _ ≤ 3*(Real.pi*smoothTransitionBound/a)^2*Real.sqrt (rawCountMoment ψ y (32*a)) := he
         _ ≤ 3*(Real.pi*smoothTransitionBound/a)^2*(C*m) := by gcongr
         _ = 3*(Real.pi*smoothTransitionBound)^2*C*(m/a^2) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hma (by positivity)
  have hb : localDensityBudget ψ q ≤ sharpOrdinaryDensityConstant*(m^2/a) := by
    unfold localDensityBudget
    have h1 := mul_le_mul_of_nonneg_left hn' (by norm_num : (0:ℝ) ≤ 32)
    have h2 := mul_le_mul_of_nonneg_left (add_le_add hg' he') (by norm_num : (0:ℝ) ≤ 4096/3)
    apply (add_le_add h1 h2).trans_eq
    dsimp only [sharpOrdinaryDensityConstant,C]
    ring
  have hloc := ordinaryDensity_local_lt ψ hψ q hq
  have hi0 : Integrable (fun z => (ordinaryDensity ψ z)^(5/3:ℝ)) := by
    have hh := (ordinaryDensity_memLp hψ).integrable_norm_rpow (by norm_num : (5/3:ENNReal) ≠ 0)
      (ENNReal.div_ne_top (by norm_num) (by norm_num) : (5/3:ENNReal) ≠ ⊤)
    simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat,Real.norm_of_nonneg (ordinaryDensity_nonneg ψ _)] using hh
  have hi : Integrable (fun z => (q.value z^2*ordinaryDensity ψ z)^(5/3:ℝ)) := by
    apply hi0.mono' ((((q.regular.continuous.pow 2).measurable.mul
      (ordinaryDensity_measurable ψ)).pow_const (5/3:ℝ)).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      simp only [Pi.mul_apply,Pi.pow_apply]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (mul_nonneg (sq_nonneg _) (ordinaryDensity_nonneg ψ z)) _)]
      apply Real.rpow_le_rpow (mul_nonneg (sq_nonneg _) (ordinaryDensity_nonneg ψ z)) _ (by norm_num)
      have hq2 : q.value z^2 ≤ 1 := by nlinarith [hq z,abs_nonneg (q.value z),sq_abs (q.value z)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hq2 (ordinaryDensity_nonneg ψ z))
  have heq : (∫ z in ball y (4*a), (ordinaryDensity ψ z)^(5/3:ℝ)) =
      ∫ z in ball y (4*a), (q.value z^2*ordinaryDensity ψ z)^(5/3:ℝ) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    have hz' : ‖z-y‖ ≤ 4*a := (by simpa only [mem_ball,dist_eq_norm] using hz : ‖z-y‖ < 4*a).le
    have hq1 : q.value z = 1 := by
      change Real.cos (radialPhase y (4*a) a z) = 1
      rw [radialPhase_zero (by positivity) ha hz',Real.cos_zero]
    dsimp only
    rw [hq1,one_pow,one_mul]
  rw [heq]
  apply (setIntegral_le_integral hi (ae_of_all _ (fun z => Real.rpow_nonneg
    (mul_nonneg (sq_nonneg _) (ordinaryDensity_nonneg ψ z)) _))).trans
  exact (hloc.trans hb).trans_eq (by ring)

end CoulombAtom

end

end OAI
