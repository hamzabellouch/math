import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.TFPriceData

namespace OAI

noncomputable section

namespace CoulombAnalysis

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
section
open CoulombAtom

lemma tfBallFunctional_convex (R Z η : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ConvexOn ℝ univ (tfBallFunctional R T Z η) := by
  refine ⟨convex_univ, ?_⟩
  intro f _ g _ a b ha hb hab
  have hn : ‖a • f + b • g‖ ≤ a*‖f‖ + b*‖g‖ := by
    simpa only [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] using norm_add_le (a • f) (b • g)
  have hk := (Real.rpow_le_rpow (norm_nonneg _) hn (by norm_num : (0:ℝ) ≤ 5/3)).trans
    ((convexOn_rpow (by norm_num : (1:ℝ) ≤ 5/3)).2 (norm_nonneg f) (norm_nonneg g) ha hb hab)
  have hd := mul_nonneg (mul_nonneg ha hb) (tfCoulombL_nonneg R (f-g))
  have he : a * tfCoulombL R f f + b * tfCoulombL R g g -
      tfCoulombL R (a • f+b • g) (a • f+b • g) = a*b*tfCoulombL R (f-g) (f-g) := by
    simp only [map_smul, map_add, map_sub, smul_apply, add_apply, sub_apply, smul_eq_mul]
    rw [tfCoulombL_symmetric R g f]
    have := hab
    nlinarith [show (a+b-1)*tfCoulombL R f f = 0 by rw [hab]; ring,
      show (a+b-1)*tfCoulombL R g g = 0 by rw [hab]; ring]
  have hh := mul_le_mul_of_nonneg_left hk hT
  rw [← he] at hd
  unfold tfBallFunctional
  simp only [map_smul, map_add, smul_apply, add_apply, smul_eq_mul] at hd hh ⊢
  nlinarith

lemma tfAdmissible_extension {M R : ℝ} {ρ : TFSpace → ℝ} (hρ : TFAdmissible M ρ)
    (hs : ∀ x, R ≤ ‖x‖ → ρ x = 0) :
    ∃ f : TFLp (ballMeasure R), NonnegDensity f ∧ tfExtension R f =ᵐ[volume] ρ := by
  obtain ⟨f, hf, he⟩ := tfAdmissible_truncate hρ R
  refine ⟨f, hf, he.trans (Eventually.of_forall fun x => ?_)⟩
  by_cases hx : ‖x‖ < R
  · rw [indicator_of_mem (show x ∈ ball (0:TFSpace) R by simpa using hx)]
  · rw [indicator_of_notMem (show x ∉ ball (0:TFSpace) R by simpa using hx), hs x (le_of_not_gt hx)]

lemma tfExtension_add_smul (R : ℝ) (a b : ℝ) (f g : TFLp (ballMeasure R)) :
    tfExtension R (a • f+b • g) =ᵐ[volume] fun x => a*tfExtension R f x+b*tfExtension R g x := by
  have he := (Lp.coeFn_add (a • f) (b • g)).trans
    (((Lp.coeFn_smul a f).add (Lp.coeFn_smul b g)).mono fun _ h => h)
  have he' := (ae_restrict_iff' measurableSet_ball).mp he
  filter_upwards [he'] with x hx
  by_cases hxb : x ∈ ball (0:TFSpace) R
  · simpa only [tfExtension, indicator_of_mem hxb, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hx hxb
  · simp only [tfExtension, indicator_of_notMem hxb, mul_zero, add_zero]

lemma tf_compact_mix {M N : ℝ} {ρ σ : TFSpace → ℝ}
    (hρ : TFAdmissible M ρ) (hσ : TFAdmissible N σ)
    (hρs : ∃ R > 0, ∀ x, R ≤ ‖x‖ → ρ x = 0)
    (hσs : ∃ R > 0, ∀ x, R ≤ ‖x‖ → σ x = 0)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (Z : ℝ) :
    TFAdmissible (a*M+b*N) (fun x => a*ρ x+b*σ x) ∧
    tfFunctional Z (fun x => a*ρ x+b*σ x) ≤ a*tfFunctional Z ρ+b*tfFunctional Z σ := by
  obtain ⟨R, _hR, hRs⟩ := hρs
  obtain ⟨S, _hS, hSs⟩ := hσs
  obtain ⟨f, hf, hef⟩ := tfAdmissible_extension hρ (R := max R S)
    (fun x hx => hRs x ((le_max_left _ _).trans hx))
  obtain ⟨g, hg, heg⟩ := tfAdmissible_extension hσ (R := max R S)
    (fun x hx => hSs x ((le_max_right _ _).trans hx))
  have hn := nonnegDensity_add (nonnegDensity_smul hf ha) (nonnegDensity_smul hg hb)
  have hem : tfExtension (max R S) (a • f+b • g) =ᵐ[volume] (fun x => a*ρ x+b*σ x) := by
    filter_upwards [tfExtension_add_smul (max R S) a b f g, hef, heg] with x hm hx hy
    rw [hm, hx, hy]
  have hmass : (∫ x, tfExtension (max R S) (a • f+b • g) x) = a*M+b*N := by
    rw [integral_congr_ae hem, integral_add (hρ.2.1.const_mul a) (hσ.2.1.const_mul b),
      integral_const_mul, integral_const_mul, hρ.2.2.1, hσ.2.2.1]
  constructor
  · have hh := tfAdmissible_congr (tfExtension_admissible hn) hem
    rwa [hmass] at hh
  · have hh := (tfBallFunctional_convex (max R S) Z 0 tfKinetic_pos.le).2
      (mem_univ f) (mem_univ g) ha hb hab
    rw [← tfExtension_functional hn Z 0, ← tfExtension_functional hf Z 0,
      ← tfExtension_functional hg Z 0] at hh
    simpa only [zero_mul, add_zero, smul_eq_mul, tfFunctional_congr_ae Z hem,
      tfFunctional_congr_ae Z hef, tfFunctional_congr_ae Z heg] using hh

lemma tf_compact_mass_exists {M : ℝ} (hM : 0 ≤ M) :
    ∃ ρ : TFSpace → ℝ, TFAdmissible M ρ ∧
      (∃ R > 0, ∀ x, R ≤ ‖x‖ → ρ x = 0) := by
  let v : ℝ := (ballMeasure 1).real univ
  have hv : 0 < v := by
    apply ENNReal.toReal_pos
    · change (volume.restrict (ball (0:TFSpace) 1)) univ ≠ 0
      rw [Measure.restrict_apply_univ]
      exact ne_of_gt (isOpen_ball.measure_pos volume ⟨0, mem_ball_self (by norm_num)⟩)
    · exact ne_of_lt (measure_lt_top (ballMeasure 1) univ)
  let c := M/v
  have hc : 0 ≤ c := div_nonneg hM hv.le
  let hm : MemLp (fun _ : TFSpace => c) (5/3) (ballMeasure 1) := memLp_const c
  let f : TFLp (ballMeasure 1) := hm.toLp (fun _ => c)
  have hf : NonnegDensity f := hm.coeFn_toLp.mono (fun _ hx => hx ▸ hc)
  have he : tfExtension 1 f =ᵐ[volume] (ball (0:TFSpace) 1).indicator (fun _ => c) := by
    have hh := (ae_restrict_iff' measurableSet_ball).mp hm.coeFn_toLp
    filter_upwards [hh] with x hx
    by_cases hxb : x ∈ ball (0:TFSpace) 1
    · simpa only [tfExtension, indicator_of_mem hxb] using hx hxb
    · simp only [tfExtension, indicator_of_notMem hxb]
  have hvint : (∫ x, tfExtension 1 f x) = M := by
    rw [integral_congr_ae he, integral_indicator measurableSet_ball, integral_const]
    change v*c = M
    exact mul_div_cancel₀ _ hv.ne'
  refine ⟨tfExtension 1 f, ?_, 1, by norm_num, fun x hx => ?_⟩
  · have hh := tfExtension_admissible hf
    rwa [hvint] at hh
  · exact indicator_of_notMem (show x ∉ ball (0:TFSpace) 1 by simpa using not_lt.mpr hx) f

end

open MeasureTheory Filter Set Metric Topology
section
open CoulombAtom

lemma tfEnergy_class_nonempty {M : ℝ} (hM : 0 ≤ M) (Z : ℝ) :
    {e | ∃ ρ, TFAdmissible M ρ ∧ tfFunctional Z ρ = e}.Nonempty := by
  obtain ⟨ρ, hρ, _⟩ := tf_compact_mass_exists hM
  exact ⟨_, ρ, hρ, rfl⟩

lemma tfEnergy_class_bddBelow {Z : ℝ} (hZ : 0 < Z) (M : ℝ) :
    BddBelow {e | ∃ ρ, TFAdmissible M ρ ∧ tfFunctional Z ρ = e} := by
  let D := tfUnitData Z hZ
  refine ⟨tfFunctional Z D.density + D.mass - M, ?_⟩
  rintro e ⟨ρ, hρ, rfl⟩
  have hh := D.minimal M ρ hρ
  linarith

lemma tfEnergy_le_trial {Z M : ℝ} (hZ : 0 < Z) {ρ : TFSpace → ℝ}
    (hρ : TFAdmissible M ρ) : tfEnergy Z M ≤ tfFunctional Z ρ :=
  csInf_le (tfEnergy_class_bddBelow hZ M) ⟨ρ, hρ, rfl⟩

def tfPriceValue (Z μ : ℝ) : ℝ :=
  if hZ : 0 < Z then if hμ : 0 < μ then
    tfFunctional Z (tfPriceData hZ hμ).density + μ*((tfPriceData hZ hμ).mass-Z)
  else tfEnergy Z Z else tfEnergy Z Z

def tfPriceDeficit (Z μ : ℝ) : ℝ := μ^(3/4:ℝ)*tfUnitDeficit (Z/μ^(3/4:ℝ))

lemma tfPriceDeficit_eq {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) :
    tfPriceDeficit Z μ = Z-(tfPriceData hZ hμ).mass :=
  (tfPriceData_deficit hZ hμ).symm

lemma tfPriceValue_eq {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) :
    tfPriceValue Z μ = tfFunctional Z (tfPriceData hZ hμ).density - μ*tfPriceDeficit Z μ := by
  rw [tfPriceValue, dite_eq_left hZ, dite_eq_left hμ, tfPriceDeficit_eq hZ hμ]; ring

lemma tfPriceValue_le_trial {Z μ M : ℝ} (hZ : 0 < Z) (hμ : 0 < μ)
    {ρ : TFSpace → ℝ} (hρ : TFAdmissible M ρ) :
    tfPriceValue Z μ ≤ tfFunctional Z ρ + μ*(M-Z) := by
  have hh := (tfPriceData hZ hμ).minimal M ρ hρ
  rw [tfPriceValue_eq hZ hμ, tfPriceDeficit_eq hZ hμ]
  linarith

lemma tfPriceValue_le_energy {Z μ M : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) (hM : 0 ≤ M) :
    tfPriceValue Z μ ≤ tfEnergy Z M + μ*(M-Z) := by
  have hh : tfPriceValue Z μ - μ*(M-Z) ≤ tfEnergy Z M := by
    apply le_csInf (tfEnergy_class_nonempty hM Z)
    rintro e ⟨ρ, hρ, rfl⟩
    linarith [tfPriceValue_le_trial hZ hμ hρ]
  linarith

lemma tfPriceValue_secant {Z μ ν : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) (hν : 0 < ν) :
    tfPriceValue Z μ ≤ tfPriceValue Z ν - (μ-ν)*tfPriceDeficit Z ν := by
  have hh := tfPriceValue_le_trial hZ hμ (tfPriceData hZ hν).admissible
  rw [tfPriceValue_eq hZ hν, tfPriceDeficit_eq hZ hν]
  linarith

lemma tfPriceDeficit_zero_tendsto {Z : ℝ} (hZ : 0 < Z) :
    Tendsto (tfPriceDeficit Z) (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun μ : ℝ => TFUnitData.chargeCap 1 * μ^(3/4:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have hk : Continuous (fun μ : ℝ => TFUnitData.chargeCap 1 * μ^(3/4:ℝ)) :=
      continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num)))
    have hh : Tendsto (fun μ : ℝ => TFUnitData.chargeCap 1 * μ^(3/4:ℝ))
        (𝓝[>] 0) (𝓝 (TFUnitData.chargeCap 1 * (0:ℝ)^(3/4:ℝ))) :=
      hk.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hh
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with μ hμ
    rw [tfPriceDeficit_eq hZ hμ]
    exact (tfPriceData_deficit_bounds hZ hμ).1
  · filter_upwards [self_mem_nhdsWithin] with μ hμ
    rw [tfPriceDeficit_eq hZ hμ]
    exact (tfPriceData_deficit_bounds hZ hμ).2

lemma tfPriceValue_zero_tendsto {Z : ℝ} (hZ : 0 < Z) :
    Tendsto (tfPriceValue Z) (𝓝[>] 0) (𝓝 (tfEnergy Z Z)) := by
  obtain ⟨σ, hσ, hσs⟩ := tf_compact_mass_exists (by linarith : 0 ≤ 2*Z)
  let B := tfFunctional Z σ
  have hlower (μ : ℝ) (hμ : 0 < μ) :
      tfEnergy Z Z - (tfPriceDeficit Z μ / Z)*(B-tfEnergy Z Z) - μ*tfPriceDeficit Z μ ≤ tfPriceValue Z μ := by
    let P := tfPriceData hZ hμ
    let d := tfPriceDeficit Z μ
    have hd : 0 ≤ d := by dsimp [d]; rw [tfPriceDeficit_eq hZ hμ]; exact (tfPriceData_deficit_bounds hZ hμ).1
    have he : P.mass = Z-d := by dsimp [P, d]; rw [tfPriceDeficit_eq hZ hμ]; ring
    have hp : 0 < Z+d := by linarith
    let a := Z/(Z+d)
    let b := d/(Z+d)
    have hab : a+b=1 := by dsimp [a,b]; rw [← add_div, div_self hp.ne']
    have hm : a*P.mass+b*(2*Z)=Z := by rw [he]; dsimp [a,b]; field_simp; ring
    obtain ⟨hmix, hmixE⟩ := tf_compact_mix P.admissible hσ P.compact hσs
      (div_nonneg hZ.le hp.le) (div_nonneg hd hp.le) hab Z
    rw [hm] at hmix
    have hle := (tfEnergy_le_trial hZ hmix).trans hmixE
    have heF : tfFunctional Z P.density = tfPriceValue Z μ + μ*d := by
      rw [tfPriceValue_eq hZ hμ]; dsimp [P, d]; ring
    rw [heF] at hle
    have hle' := mul_le_mul_of_nonneg_left hle hp.le
    have hea : (Z+d)*a=Z := by dsimp [a]; exact mul_div_cancel₀ _ hp.ne'
    have heb : (Z+d)*b=d := by dsimp [b]; exact mul_div_cancel₀ _ hp.ne'
    rw [mul_add, ← mul_assoc, ← mul_assoc, hea, heb] at hle'
    change tfEnergy Z Z - (d/Z)*(B-tfEnergy Z Z)-μ*d ≤ tfPriceValue Z μ
    apply (mul_le_mul_iff_right₀ hZ).mp
    calc
      _ = (Z+d)*tfEnergy Z Z-d*B-Z*μ*d := by field_simp; ring
      _ ≤ Z * tfPriceValue Z μ := by dsimp [B]; nlinarith [hle']
  have hd := tfPriceDeficit_zero_tendsto hZ
  have hμ : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun μ => tfEnergy Z Z - (tfPriceDeficit Z μ/Z)*(B-tfEnergy Z Z) - μ*tfPriceDeficit Z μ)
      (𝓝[>] 0) (𝓝 (tfEnergy Z Z)) := by
    simpa using (tendsto_const_nhds.sub ((hd.div_const Z).mul_const (B-tfEnergy Z Z))).sub (hμ.mul hd)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with μ hμ
    exact hlower μ hμ
  · filter_upwards [self_mem_nhdsWithin] with μ hμ
    simpa using tfPriceValue_le_energy hZ hμ hZ.le

lemma tfPriceValue_zero_bounds {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) :
    -μ*tfPriceDeficit Z μ ≤ tfPriceValue Z μ-tfEnergy Z Z ∧
      tfPriceValue Z μ-tfEnergy Z Z ≤ 0 := by
  have hh : tfEnergy Z Z ≤ tfPriceValue Z μ + μ*tfPriceDeficit Z μ := by
    apply le_of_tendsto (tfPriceValue_zero_tendsto hZ)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hμ)] with ν hν hνμ
    change 0 < ν at hν
    have hs := tfPriceValue_secant hZ hν hμ
    have hd := (tfPriceData_deficit_bounds hZ hμ).1
    rw [← tfPriceDeficit_eq hZ hμ] at hd
    nlinarith
  exact ⟨by linarith, by have := tfPriceValue_le_energy hZ hμ hZ.le; linarith⟩

end

open Filter
open scoped Topology

end CoulombAnalysis

end

end OAI
