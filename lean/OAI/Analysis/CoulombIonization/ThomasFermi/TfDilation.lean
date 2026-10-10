import Mathlib
import OAI.Analysis.CoulombIonization.Model
import OAI.Analysis.CoulombIonization.ThomasFermi.Pairing

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
namespace CoulombAtom

def tfDilation (b : ℝ) (ρ : Space → ℝ) (x : Space) : ℝ := b ^ 6 * ρ (b • x)

local instance : Measure.IsAddHaarMeasure (volume : Measure (Space × Space)) := by
  change Measure.IsAddHaarMeasure ((volume : Measure Space).prod volume)
  infer_instance

lemma space_finrank : Module.finrank ℝ Space = 3 := by simp [Space]

lemma product_finrank : Module.finrank ℝ (Space × Space) = 6 := by
  rw [Module.finrank_prod, space_finrank]

lemma tfDilation_mass {b : ℝ} (hb : 0 < b) (ρ : Space → ℝ) :
    (∫ x, tfDilation b ρ x) = b ^ 3 * ∫ x, ρ x := by
  simp only [tfDilation, integral_const_mul]
  rw [Measure.integral_comp_smul_of_nonneg volume ρ b (hR := hb.le), space_finrank]
  simp only [smul_eq_mul]
  field_simp

lemma tfDilation_kinetic {b : ℝ} (hb : 0 < b) (ρ : Space → ℝ) (x : Space) (hx : 0 ≤ ρ (b • x)) :
    (tfDilation b ρ x) ^ (5 / 3 : ℝ) = b ^ 10 * ρ (b • x) ^ (5 / 3 : ℝ) := by
  rw [tfDilation, Real.mul_rpow (pow_nonneg hb.le _) hx]
  congr 1
  rw [← Real.rpow_natCast b 6, ← Real.rpow_mul hb.le]
  norm_num

lemma tfDilation_nuclear {b : ℝ} (hb : 0 < b) (ρ : Space → ℝ) (x : Space) :
    tfDilation b ρ x / ‖x‖ = b ^ 7 * (ρ (b • x) / ‖b • x‖) := by
  rw [tfDilation, norm_smul, Real.norm_of_nonneg hb.le]
  field_simp

lemma tfDilation_direct {b : ℝ} (hb : 0 < b) (ρ : Space → ℝ) (p : Space × Space) :
    directIntegrand (tfDilation b ρ) p = b ^ 13 * directIntegrand ρ (b • p) := by
  simp only [directIntegrand, tfDilation, Prod.smul_fst, Prod.smul_snd, ← smul_sub,
    norm_smul, Real.norm_of_nonneg hb.le]
  field_simp

lemma tfDilation_admissible {b : ℝ} (hb : 0 < b) {M : ℝ} {ρ : Space → ℝ}
    (hρ : TFAdmissible M ρ) : TFAdmissible (b ^ 3 * M) (tfDilation b ρ) := by
  rcases hρ with ⟨hpos, hint, hmass, hkin, hnuc, hdir⟩
  refine ⟨?_, (hint.comp_smul hb.ne').const_mul _, ?_, ?_, ?_, ?_⟩
  · filter_upwards [(Measure.quasiMeasurePreserving_smul volume hb.ne').ae hpos] with x hx
    exact mul_nonneg (pow_nonneg hb.le _) hx
  · rw [tfDilation_mass hb, hmass]
  · have he : (fun x => (tfDilation b ρ x) ^ (5 / 3 : ℝ)) =ᵐ[volume]
        (fun x => b ^ 10 * ρ (b • x) ^ (5 / 3 : ℝ)) := by
      filter_upwards [(Measure.quasiMeasurePreserving_smul volume hb.ne').ae hpos] with x hx
      exact tfDilation_kinetic hb ρ x hx
    exact ((hkin.comp_smul hb.ne').const_mul _).congr he.symm
  · simp_rw [tfDilation_nuclear hb]
    exact (hnuc.comp_smul hb.ne').const_mul _
  · change Integrable (fun p => directIntegrand (tfDilation b ρ) p)
    simp_rw [tfDilation_direct hb]
    exact (hdir.comp_smul hb.ne').const_mul _

lemma tfDilation_functional {b : ℝ} (hb : 0 < b) (Z : ℝ) (ρ : Space → ℝ)
    (hpos : ∀ᵐ x, 0 ≤ ρ x) :
    tfFunctional (b ^ 3 * Z) (tfDilation b ρ) = b ^ 7 * tfFunctional Z ρ := by
  have hk : (∫ x, (tfDilation b ρ x) ^ (5 / 3 : ℝ)) =
      b ^ 10 * ∫ x, ρ (b • x) ^ (5 / 3 : ℝ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(Measure.quasiMeasurePreserving_smul volume hb.ne').ae hpos] with x hx
    exact tfDilation_kinetic hb ρ x hx
  simp only [tfFunctional, hk, tfDilation_nuclear hb, tfDilation_direct hb, integral_const_mul]
  rw [Measure.integral_comp_smul_of_nonneg volume (fun x : Space => ρ x ^ (5 / 3 : ℝ)) b (hR := hb.le),
    Measure.integral_comp_smul_of_nonneg volume (fun x : Space => ρ x / ‖x‖) b (hR := hb.le),
    Measure.integral_comp_smul_of_nonneg volume (directIntegrand ρ) b (hR := hb.le),
    space_finrank, product_finrank]
  simp only [smul_eq_mul]
  field_simp

lemma tfDilation_inv {b : ℝ} (hb : b ≠ 0) (ρ : Space → ℝ) :
    tfDilation b (tfDilation b⁻¹ ρ) = ρ := by
  funext x
  simp [tfDilation, smul_smul, hb]

theorem tfEnergy_scaling {b : ℝ} (hb : 0 < b) (Z M : ℝ) :
    tfEnergy (b ^ 3 * Z) (b ^ 3 * M) = b ^ 7 * tfEnergy Z M := by
  have hs : {e | ∃ ρ : Space → ℝ, TFAdmissible (b ^ 3 * M) ρ ∧
        tfFunctional (b ^ 3 * Z) ρ = e} =
      (b ^ 7) • {e | ∃ ρ : Space → ℝ, TFAdmissible M ρ ∧ tfFunctional Z ρ = e} := by
    ext e
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      have hi : TFAdmissible M (tfDilation b⁻¹ ρ) := by
        have h := tfDilation_admissible (inv_pos.mpr hb) hρ
        simpa only [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hb.ne'), one_mul] using h
      refine ⟨tfFunctional Z (tfDilation b⁻¹ ρ), ⟨tfDilation b⁻¹ ρ, hi, rfl⟩, ?_⟩
      change b ^ 7 * tfFunctional Z (tfDilation b⁻¹ ρ) = tfFunctional (b ^ 3 * Z) ρ
      rw [← tfDilation_functional hb Z _ hi.1, tfDilation_inv hb.ne']
    · rintro ⟨e', ⟨ρ, hρ, rfl⟩, rfl⟩
      exact ⟨tfDilation b ρ, tfDilation_admissible hb hρ, tfDilation_functional hb Z ρ hρ.1⟩
  unfold tfEnergy
  rw [hs, Real.sInf_smul_of_nonneg (pow_nonneg hb.le _)]
  rfl

theorem tfIonization_scaling {m : ℝ} (hm : 0 < m) (Z : ℝ) :
    tfIonization m Z = m ^ (7 / 3 : ℝ) * tfIonization 1 (Z / m) := by
  let b : ℝ := m ^ (1 / 3 : ℝ)
  have hb : 0 < b := Real.rpow_pos_of_pos hm _
  have hb3 : b ^ 3 = m := by
    dsimp [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]
    norm_num
  have hb7 : b ^ 7 = m ^ (7 / 3 : ℝ) := by
    dsimp [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]
    norm_num
  have hZ : b ^ 3 * (Z / m) = Z := by
    rw [hb3]
    field_simp
  have he (N : ℝ) : tfEnergy Z (m * N) = m ^ (7 / 3 : ℝ) * tfEnergy (Z / m) N := by
    have ht := tfEnergy_scaling hb (Z / m) N
    rw [hZ, hb3, hb7] at ht
    exact ht
  calc
    tfIonization m Z = tfEnergy Z (m * (Z / m - 1)) - tfEnergy Z (m * (Z / m)) := by
      unfold tfIonization
      congr 2 <;> field_simp
    _ = _ := by rw [he, he, tfIonization]; ring

theorem tfCharacterization_of_unit_limit {a : ℝ}
    (ha : Tendsto (tfIonization 1) atTop (𝓝 a)) : TFCharacterization a := by
  intro m hm
  have hdiv : Tendsto (fun Z : ℝ => Z / m) atTop atTop :=
    Filter.Tendsto.atTop_div_const hm tendsto_id
  have h := (ha.comp hdiv).const_mul (m ^ (7 / 3 : ℝ))
  simpa only [Function.comp_def, ← tfIonization_scaling hm, mul_comm (m ^ (7 / 3 : ℝ)) a] using h

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace CoulombAnalysis
open CoulombAtom

lemma tfKinetic_pos : 0 < tfKinetic := by
  unfold tfKinetic
  positivity

lemma tfExtension_nonneg {R : ℝ} {f : TFLp (ballMeasure R)} (hf : NonnegDensity f) :
    ∀ᵐ x, 0 ≤ tfExtension R f x := by
  have hh := (ae_restrict_iff' measurableSet_ball).mp hf
  filter_upwards [hh] with x hx
  by_cases hx' : x ∈ ball (0 : TFSpace) R
  · simpa [tfExtension, hx'] using hx hx'
  · simp [tfExtension, hx']

lemma tfExtension_kinetic (R : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) :
    tfExtension R f x ^ (5 / 3 : ℝ) =
      (ball 0 R).indicator (fun x => f x ^ (5 / 3 : ℝ)) x := by
  classical
  by_cases hx : x ∈ ball (0 : TFSpace) R <;> simp [tfExtension, hx]

lemma tfExtension_nuclear (R : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) :
    tfExtension R f x / ‖x‖ = (ball 0 R).indicator (fun x => f x / ‖x‖) x := by
  classical
  by_cases hx : x ∈ ball (0 : TFSpace) R <;> simp [tfExtension, hx]

lemma tfExtension_kinetic_integrable {R : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) : Integrable (fun x => tfExtension R f x ^ (5 / 3 : ℝ)) := by
  simp_rw [tfExtension_kinetic]
  exact IntegrableOn.integrable_indicator (tf_integrable (Lp.memLp f) hf) measurableSet_ball

lemma tfExtension_nuclear_integrable (R : ℝ) (f : TFLp (ballMeasure R)) :
    Integrable (fun x => tfExtension R f x / ‖x‖) := by
  simp_rw [tfExtension_nuclear]
  apply IntegrableOn.integrable_indicator _ measurableSet_ball
  simpa only [div_eq_inv_mul, ballMeasure, IntegrableOn] using tfPairing_integrable _ (nuclear_memLp R) f

lemma tfExtension_admissible {R : ℝ} {f : TFLp (ballMeasure R)} (hf : NonnegDensity f) :
    TFAdmissible (∫ x, tfExtension R f x) (tfExtension R f) :=
  ⟨tfExtension_nonneg hf, tfExtension_integrable R f, rfl,
    tfExtension_kinetic_integrable hf, tfExtension_nuclear_integrable R f,
    tfExtension_coulomb_integrable R f f⟩

lemma tfExtension_functional {R : ℝ} {f : TFLp (ballMeasure R)} (hf : NonnegDensity f)
    (Z η : ℝ) : tfFunctional Z (tfExtension R f) + η * (∫ x, tfExtension R f x) =
      tfBallFunctional R tfKinetic Z η f := by
  unfold tfFunctional tfBallFunctional tfBallLinear
  rw [tfLp_norm_rpow_nonneg hf, tfCoulombL_extension]
  simp only [sub_apply, smul_apply,
    smul_eq_mul, tfPairing_apply, one_mul]
  have hk : (∫ x, (tfExtension R f x) ^ (5 / 3 : ℝ)) =
      ∫ x, f x ^ (5 / 3 : ℝ) ∂ballMeasure R := by
    simp_rw [tfExtension_kinetic]
    exact integral_indicator measurableSet_ball
  have hn : (∫ x, tfExtension R f x / ‖x‖) =
      ∫ x, ‖x‖⁻¹ * f x ∂ballMeasure R := by
    simp_rw [tfExtension_nuclear, div_eq_inv_mul]
    exact integral_indicator measurableSet_ball
  rw [hk, hn, show (∫ x, tfExtension R f x) = ∫ x, f x ∂ballMeasure R from
    integral_indicator measurableSet_ball]
  dsimp only [directIntegrand]
  ring

lemma tfAdmissible_memLp {M : ℝ} {ρ : Space → ℝ} (hρ : TFAdmissible M ρ) :
    MemLp ρ (5 / 3) := by
  apply (integrable_norm_rpow_iff hρ.2.1.aestronglyMeasurable
    (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num
  exact hρ.2.2.2.1.congr (hρ.1.mono fun x hx => by dsimp; rw [abs_of_nonneg hx])

lemma tfAdmissible_truncate {M : ℝ} {ρ : Space → ℝ} (hρ : TFAdmissible M ρ) (R : ℝ) :
    ∃ f : TFLp (ballMeasure R), NonnegDensity f ∧ tfExtension R f =ᵐ[volume]
      (ball 0 R).indicator ρ := by
  let hm : MemLp ρ (5 / 3) (ballMeasure R) := (tfAdmissible_memLp hρ).restrict _
  refine ⟨hm.toLp ρ, ?_, ?_⟩
  · filter_upwards [hm.coeFn_toLp, ae_restrict_of_ae hρ.1] with x he hx
    rw [he]
    exact hx
  · have hh := (ae_restrict_iff' measurableSet_ball).mp hm.coeFn_toLp
    filter_upwards [hh] with x hx
    by_cases hx' : x ∈ ball (0 : TFSpace) R
    · simpa [tfExtension, hx'] using hx hx'
    · simp [tfExtension, hx']

lemma tfFunctional_congr_ae (Z : ℝ) {ρ σ : Space → ℝ} (he : ρ =ᵐ[volume] σ) :
    tfFunctional Z ρ = tfFunctional Z σ := by
  have hk := integral_congr_ae (he.fun_comp fun t => t ^ (5 / 3 : ℝ))
  dsimp only [Function.comp_def] at hk
  have hn := integral_congr_ae (he.mono fun x hx => congrArg (fun t => t / ‖x‖) hx)
  have hd : directIntegrand ρ =ᵐ[volume] directIntegrand σ := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae he,
      Measure.quasiMeasurePreserving_snd.ae he] with p h1 h2
    simp only [directIntegrand, h1, h2]
  simp only [tfFunctional, hk, hn, integral_congr_ae hd]

lemma tfIndicator_direct (R : ℝ) (ρ : Space → ℝ) (p : Space × Space) :
    directIntegrand ((ball 0 R).indicator ρ) p =
      ((ball (0 : Space) R) ×ˢ ball 0 R).indicator (directIntegrand ρ) p := by
  classical
  by_cases h1 : p.1 ∈ ball (0 : Space) R <;>
    by_cases h2 : p.2 ∈ ball (0 : Space) R <;> simp [directIntegrand, h1, h2]

lemma tfIndicator_kinetic (R : ℝ) (ρ : Space → ℝ) (x : Space) :
    ((ball 0 R).indicator ρ x) ^ (5 / 3 : ℝ) =
      (ball 0 R).indicator (fun x => ρ x ^ (5 / 3 : ℝ)) x := by
  classical
  by_cases hx : x ∈ ball (0 : Space) R <;> simp [hx]

lemma tfIndicator_linear (R Z : ℝ) (ρ : Space → ℝ) (x : Space) :
    (ball 0 R).indicator ρ x - Z * ((ball 0 R).indicator ρ x / ‖x‖) =
      (ball 0 R).indicator (fun x => ρ x - Z * (ρ x / ‖x‖)) x := by
  classical
  by_cases hx : x ∈ ball (0 : Space) R <;> simp [hx]

lemma tfPriced_truncate_le {Z M : ℝ} (hZ : 0 < Z) {ρ : Space → ℝ}
    (hρ : TFAdmissible M ρ) :
    tfFunctional Z ((ball 0 Z).indicator ρ) + (∫ x, (ball 0 Z).indicator ρ x) ≤
      tfFunctional Z ρ + (∫ x, ρ x) := by
  have hk : (∫ x, ((ball 0 Z).indicator ρ x) ^ (5 / 3 : ℝ)) ≤
      ∫ x, ρ x ^ (5 / 3 : ℝ) := by
    simp_rw [tfIndicator_kinetic]
    apply integral_mono_ae (hρ.2.2.2.1.indicator measurableSet_ball) hρ.2.2.2.1
    filter_upwards [hρ.1] with x hx
    by_cases hxb : x ∈ ball (0 : Space) Z
    · simp [hxb]
    · simpa only [indicator_of_notMem hxb] using Real.rpow_nonneg hx (5 / 3 : ℝ)
  have hd : (∫ p, directIntegrand ((ball 0 Z).indicator ρ) p) ≤
      ∫ p, directIntegrand ρ p := by
    simp_rw [tfIndicator_direct]
    apply integral_mono_ae (hρ.2.2.2.2.2.indicator (measurableSet_ball.prod measurableSet_ball)) hρ.2.2.2.2.2
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hρ.1,
      Measure.quasiMeasurePreserving_snd.ae hρ.1] with p h1 h2
    by_cases hp : p ∈ (ball (0 : Space) Z) ×ˢ ball 0 Z
    · simp [hp]
    · simp only [indicator_of_notMem hp]
      exact div_nonneg (mul_nonneg h1 h2) (norm_nonneg _)
  have hlin := hρ.2.1.sub (hρ.2.2.2.2.1.const_mul Z)
  have hnuc : Integrable (fun x => (ball 0 Z).indicator ρ x / ‖x‖) := by
    have he : (fun x => (ball (0 : Space) Z).indicator ρ x / ‖x‖) =
        (ball 0 Z).indicator (fun x => ρ x / ‖x‖) := by
      ext x
      by_cases hx : x ∈ ball (0 : Space) Z <;> simp [hx]
    rw [he]
    exact hρ.2.2.2.2.1.indicator measurableSet_ball
  have hl : (∫ x, (ball 0 Z).indicator ρ x) - Z * (∫ x, (ball 0 Z).indicator ρ x / ‖x‖) ≤
      (∫ x, ρ x) - Z * (∫ x, ρ x / ‖x‖) := by
    rw [← integral_const_mul, ← integral_sub (hρ.2.1.indicator measurableSet_ball) (hnuc.const_mul Z),
      ← integral_const_mul, ← integral_sub hρ.2.1 (hρ.2.2.2.2.1.const_mul Z)]
    simp_rw [tfIndicator_linear]
    apply integral_mono_ae (hlin.indicator measurableSet_ball) hlin
    filter_upwards [hρ.1] with x hx
    by_cases hx' : x ∈ ball (0 : Space) Z
    · simp [hx']
    · rw [indicator_of_notMem hx']
      have hr : Z ≤ ‖x‖ := le_of_not_gt (mt mem_ball_zero_iff.mpr hx')
      have hr0 := hZ.trans_le hr
      have hh : Z / ‖x‖ ≤ 1 := (div_le_one hr0).mpr hr
      dsimp only [Pi.sub_apply]
      have he : Z * (ρ x / ‖x‖) = (Z / ‖x‖) * ρ x := by ring
      rw [he]
      linarith [mul_le_mul_of_nonneg_right hh hx]
  unfold tfFunctional
  nlinarith [mul_le_mul_of_nonneg_left hk tfKinetic_pos.le]

theorem tf_unit_price_exists_minimizer (Z : ℝ) (hZ : 0 < Z) :
    ∃ M : ℝ, ∃ ρ : Space → ℝ, TFAdmissible M ρ ∧
      ∀ M' : ℝ, ∀ σ : Space → ℝ, TFAdmissible M' σ →
        tfFunctional Z ρ + M ≤ tfFunctional Z σ + M' := by
  obtain ⟨f, hf, hmin⟩ := tfBallFunctional_exists_minimizer Z Z 1 tfKinetic_pos
  refine ⟨_, tfExtension Z f, tfExtension_admissible hf, fun M' σ hσ => ?_⟩
  obtain ⟨g, hg, he⟩ := tfAdmissible_truncate hσ Z
  have hh := hmin g hg
  rw [← tfExtension_functional hf Z 1, ← tfExtension_functional hg Z 1, one_mul, one_mul,
    tfFunctional_congr_ae Z he, integral_congr_ae he] at hh
  exact hh.trans (by simpa only [hσ.2.2.1] using tfPriced_truncate_le hZ hσ)

end CoulombAnalysis

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

end

end OAI
