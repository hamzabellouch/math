import Mathlib
import OAI.Probability.SKFluctuations.MartingaleCompensatorLp

namespace OAI

/-! Scalar Flattened Continuity. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarFlattenedEnergy_tendsto {T m : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    {p r : ℕ → ℝ} {q : ℝ} (hp : Tendsto p atTop (𝓝 q)) (hr : Tendsto r atTop (𝓝 q))
    (hpr : ∀ k, p k ≤ r k) :
    Tendsto (fun k => scalarFlattenedEnergy hT α (p k) (r k) hm) atTop
      (𝓝 (scalarPlantedEnergy hT α q)) := by
  have ht : Tendsto (fun k => T*(r k-p k)) atTop (𝓝 0) := by
    simpa only [sub_self,mul_zero] using (hr.sub hp).const_mul T
  have hJ := HeatJet.evolve_small_terminal_tendsto
    (fun k => (scalarTailJet hT α (r k)).square) (scalarTailJet hT α q).square
    (scalarTailJet_F_tendsto hT α hr) (scalarTailJet_square_tendsto hT α hr) hm hm1
    (fun k => T*(r k-p k)) (fun k => mul_nonneg hT.le (sub_nonneg.mpr (hpr k))) ht
  let A := rescaledMassProfile α hT
  have hA (s : ℝ) : A.mass s ≤ 1 := (α.property.1 (s/T)).2
  have hd := HeatJet.nonnegativeProfileTest_terminal_tendsto
    (fun k => ((scalarTailJet hT α (r k)).square.evolve hm (T*(r k-p k))))
    (scalarTailJet hT α q).square hJ.1 hJ.2 (fun _ => A) (fun _ => hA)
    (fun _ => 0) (fun k => Real.toNNReal (T*p k))
  have hl := ((scalarTailJet hT α q).square.nonnegativeProfileTest_window_continuous A hA 0).tendsto
    (0,Real.toNNReal (T*q)) |>.comp
      (tendsto_const_nhds.prodMk_nhds (continuous_real_toNNReal.tendsto (T*q) |>.comp (hp.const_mul T)))
  have hh := (hd.tendsto_at 0).add hl
  simpa only [Function.comp_def,sub_add_cancel,zero_add,scalarFlattenedEnergy,scalarPlantedEnergy,A] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarPrefixTest_envelope {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hq1 : q ≤ 1) (hm : 0 < α.val q)
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x)
    (A : (Fin 1 → ℝ) → ℝ) (hA : BddSmooth 2 A) (hp : ∀ y, 0 ≤ A y) :
    (∫ x, gaussianLinearEnvelope (T*q) (-2) x*A (fun _ => x))/gaussianLinearEnvelopeMass (T*q) 2 ≤
      ((scalarTailJet hT α q).withTest A hA).nonnegativeProfileTest
        (rescaledMassProfile α hT) 0 (Real.toNNReal (T*q)) 0 ∧
    ((scalarTailJet hT α q).withTest A hA).nonnegativeProfileTest
        (rescaledMassProfile α hT) 0 (Real.toNNReal (T*q)) 0 ≤
      (∫ x, gaussianLinearEnvelope (T*q) 2 x*A (fun _ => x))/gaussianLinearEnvelopeMass (T*q) (-2) := by
  obtain ⟨R,hv,_hR,hg,hn,ht⟩ := scalarPrefixResidualApproximation hT α hq hq1 hm hc
  let F := fun y => (scalarTailJet hT α q).F (fun _ => y)
  have hF : LipschitzWith 1 F := scalar_restrict_lipschitz (scalarTailJet hT α q).lipschitz
  have hs : 0 < T*q := mul_pos hT hq
  have hAc : Continuous (fun x : ℝ => A (fun _ => x)) :=
    hA.continuous.comp (continuous_pi fun _ => continuous_id)
  obtain ⟨B,_hB,hB⟩ := hA.bound
  have hi (a b : ℝ) : Integrable (fun x =>
      gaussianLinearEnvelope (T*q) a x/gaussianLinearEnvelopeMass (T*q) b*A (fun _ => x)) :=
    ((gaussianLinearEnvelope_integrable hs a).div_const _).mul_bdd hAc.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB (fun _ => x))
  have he (a b : ℝ) : (∫ x, gaussianLinearEnvelope (T*q) a x/
      gaussianLinearEnvelopeMass (T*q) b*A (fun _ => x))=
      (∫ x, gaussianLinearEnvelope (T*q) a x*A (fun _ => x))/gaussianLinearEnvelopeMass (T*q) b := by
    simp_rw [div_mul_eq_mul_div]
    exact integral_div _ _
  have hiN (N : ℕ) : Integrable (fun x => (R N).plantedDensity F (α.val q) x*A (fun _ => x)) :=
    ((R N).plantedDensity_integrable hF (α.val q)).mul_bdd hAc.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB (fun _ => x))
  have henv (N : ℕ) (x : ℝ) := (R N).plantedDensity_envelope (hg N) hF
    (by simpa only [abs_of_pos hm] using (α.property.1 q).2) (hn N) x
  constructor
  · apply ge_of_tendsto (ht A hA)
    apply Eventually.of_forall
    intro N
    rw [← he (-2) 2]
    apply integral_mono (hi _ _) (hiN N)
    intro x
    have hh := (henv N x).1
    rw [hv N] at hh
    exact mul_le_mul_of_nonneg_right hh (hp _)
  · apply le_of_tendsto (ht A hA)
    apply Eventually.of_forall
    intro N
    rw [← he 2 (-2)]
    apply integral_mono (hiN N) (hi _ _)
    intro x
    have hh := (henv N x).2
    rw [hv N] at hh
    exact mul_le_mul_of_nonneg_right hh (hp _)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem scalarTailJet_origin_curvature_derivative {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s) :
    HasDerivWithinAt (fun q => (scalarTailJet hT α q).H 0 0)
      (-(T/2)*(scalarTailSpatialJet hT α 4 0 0+
        2*α.val 0*((scalarTailJet hT α 0).H 0 0)^2)) (Ioi 0) 0 := by
  let C : ℝ → ℝ := fun q => T*scalarTailCurvatureRate hT α q 1 (T*q)
  have hC : Continuous C := by
    have hz : Continuous (fun q : ℝ => (T*q,(q,(1:ℝ)))) := by fun_prop
    exact ((scalarTailCurvatureRate_continuous hT α).comp hz).const_mul T
  have hd := (scalarTailJet_flatten_curvature_hasDerivWithinAt hT (q:=0) le_rfl
    zero_lt_one α zero_lt_one le_rfl hc 0).mono Ioi_subset_Ici_self
  have ha : (((scalarTailJet hT α 0).square).evolve zero_lt_one (T*0)).A₂ 0 0 =
      2*((scalarTailJet hT α 0).H 0 0)^2 := by
    simp only [mul_zero,HeatJet.evolve,clockSecond,clockGradient,clockTest_zero]
    simp only [HeatJet.square,scalarTailJet_A_zero]
    change _ = 2*((scalarTailJet hT α 0).A₁ 0 0)^2
    ring
  change HasDerivWithinAt (fun r => ((scalarTailJet hT α r).evolve zero_lt_one (T*r)).H 0 0)
    (T/2*((1-α.val 0)*(((scalarTailJet hT α 0).square).evolve zero_lt_one (T*0)).A₂ 0 0)) _ _ at hd
  rw [ha] at hd
  have he := hd.sub (right_deriv_mul_continuous hC.continuousWithinAt)
  have hd' : -(T/2)*(scalarTailSpatialJet hT α 4 0 0+
      2*α.val 0*((scalarTailJet hT α 0).H 0 0)^2) =
      T/2*((1-α.val 0)*(2*((scalarTailJet hT α 0).H 0 0)^2))-C 0 := by
    dsimp only [C]
    rw [mul_zero,scalarTailCurvatureRate_zero,unitMassClip_eq (show (1:ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_rfl⟩)]
    ring
  rw [hd']
  apply he.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with q hq
    have hx := scalarTailCurvatureRate_eq hT α (q:=q) zero_lt_one le_rfl (mul_nonneg hT.le hq.le)
    change (scalarTailJet hT α q).H 0 0 =
      ((scalarTailJet hT α q).evolve zero_lt_one (T*q)).H 0 0-q*C q
    dsimp only [C]
    rw [hx]
    ring
  · change (scalarTailJet hT α 0).H 0 0 =
      ((scalarTailJet hT α 0).evolve zero_lt_one (T*0)).H 0 0-0*C 0
    simp only [zero_mul,sub_zero,mul_zero]
    have hx := scalarTailCurvatureRate_eq hT α (q:=0) zero_lt_one le_rfl (t:=0) le_rfl
    simpa only [zero_mul,add_zero] using hx.symm

 

theorem scalarTailJet_zero_mass_curvature_derivative {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hc : ∀ s, ContinuousWithinAt α.val (Ici s) s)
    (hzero : α.val 0=0) :
    HasDerivWithinAt (fun q => (scalarTailJet hT α q).H 0 0)
      (-(T/2)*scalarTailSpatialJet hT α 4 0 0) (Ioi 0) 0 ∧
      0 < -(T/2)*scalarTailSpatialJet hT α 4 0 0 := by
  constructor
  · simpa only [hzero,mul_zero,zero_mul,add_zero] using
      scalarTailJet_origin_curvature_derivative hT α hc
  · exact mul_pos_of_neg_of_neg (neg_neg_of_pos (div_pos hT (by norm_num)))
      (scalarProfileJet_four_zero_neg (rescaledMassProfile α hT)
        (fun s => (α.property.1 (s/T)).2) _ _)

 

noncomputable def scalarInitialDensityConstant {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) : ℝ :=
  T*(scalarTailSpatialJet hT α 4 0 0)^2/(2*((scalarTailJet hT α 0).H 0 0)^3)

theorem scalarInitialDensityConstant_pos {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) : 0 < scalarInitialDensityConstant hT α := by
  have h4 : scalarTailSpatialJet hT α 4 0 0 < 0 :=
    scalarProfileJet_four_zero_neg (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) _ _
  have h2 : 0 < (scalarTailJet hT α 0).H 0 0 :=
    scalarProfileJet_curvature_pos (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) _ _ _
  exact div_pos (mul_pos hT (sq_pos_of_ne_zero h4.ne))
    (mul_pos (by norm_num) (pow_pos h2 3))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarPlantedThirdSquare_envelope {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hq1 : q ≤ 1) (hm : 0 < α.val q)
    (hc : ∀ x ∈ Ico (0:ℝ) q, ContinuousWithinAt α.val (Ici x) x) :
    scalarThirdGaussianEnvelope hT α (-2) q/gaussianLinearEnvelopeMass (T*q) 2 ≤
      scalarPlantedJetPower hT α 2 2 q/q ∧
    scalarPlantedJetPower hT α 2 2 q/q ≤
      scalarThirdGaussianEnvelope hT α 2 q/gaussianLinearEnvelopeMass (T*q) (-2) := by
  have hh := scalarPrefixTest_envelope hT α hq hq1 hm hc
    (fun y => (scalarTailSpatialJet hT α 3 q y)^2)
    ((scalarTailSpatialJet_bddSmooth_all hT α 2 2 q).pow 2) (fun _ => sq_nonneg _)
  constructor
  · have hl := div_le_div_of_nonneg_right hh.1 hq.le
    simpa only [scalarThirdGaussianEnvelope,scalarPlantedJetPower,scalarJetPowerTest,
      div_div,mul_comm] using hl
  · have hl := div_le_div_of_nonneg_right hh.2 hq.le
    simpa only [scalarThirdGaussianEnvelope,scalarPlantedJetPower,scalarJetPowerTest,
      div_div,mul_comm] using hl

theorem scalarPlantedThirdSquare_initial_limit {T Q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x)
    (hp : ∀ q ∈ Ioo (0:ℝ) Q, 0 < α.val q) :
    Tendsto (fun q => scalarPlantedJetPower hT α 2 2 q/q) (𝓝[>] 0)
      (𝓝 (T*(scalarTailSpatialJet hT α 4 0 0)^2)) := by
  have hl := (scalarThirdGaussianEnvelope_tendsto hT α (-2)).div
    (gaussianLinearEnvelopeMass_tendsto hT 2) one_ne_zero
  have hu := (scalarThirdGaussianEnvelope_tendsto hT α 2).div
    (gaussianLinearEnvelopeMass_tendsto hT (-2)) one_ne_zero
  simp only [div_one] at hl hu
  have hh : ∀ᶠ q : ℝ in 𝓝[>] 0,
      scalarThirdGaussianEnvelope hT α (-2) q/gaussianLinearEnvelopeMass (T*q) 2 ≤
        scalarPlantedJetPower hT α 2 2 q/q ∧
      scalarPlantedJetPower hT α 2 2 q/q ≤
        scalarThirdGaussianEnvelope hT α 2 q/gaussianLinearEnvelopeMass (T*q) (-2) := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hQ)] with q hq hqQ
    exact scalarPlantedThirdSquare_envelope hT α hq (hqQ.le.trans hQ1)
      (hp q ⟨hq,hqQ⟩) (fun x _ => hc x)
  exact hl.squeeze' hu (hh.mono fun _ hx => hx.1) (hh.mono fun _ hx => hx.2)

theorem scalarPlantedJetPower_zero {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (k p : ℕ) :
    scalarPlantedJetPower hT α k p 0=(scalarTailSpatialJet hT α (k+1) 0 0)^p := by
  unfold scalarPlantedJetPower
  rw [mul_zero,Real.toNNReal_zero,HeatJet.nonnegativeProfileTest_zero _ _
    (fun s => (α.property.1 (s/T)).2)]
  rfl

theorem scalarSupport_cdf_initial_limit {T Q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hQ : 0 < Q) (hQ1 : Q < 1)
    (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x)
    (hs : (profileStieltjes α).measure.support=Icc 0 Q)
    (hmar : ∀ x ∈ Icc 0 Q, T*scalarPlantedCurvature hT α x=1) :
    Tendsto (fun q => α.val q/q) (𝓝[>] 0) (𝓝 (scalarInitialDensityConstant hT α)) := by
  have hnum := scalarPlantedThirdSquare_initial_limit hT α hQ hQ1.le hc
    (fun q hq => scalarSupport_cdf_positive α hc hs ⟨hq.1,hq.2.le⟩)
  have hden : Tendsto (scalarPlantedJetPower hT α 1 3) (𝓝[>] 0)
      (𝓝 (scalarPlantedJetPower hT α 1 3 0)) :=
    ((scalarPlantedJetPower_continuous hT α 1 3).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [scalarPlantedJetPower_zero] at hden
  have hp : 0 < scalarTailSpatialJet hT α 2 0 0 :=
    scalarProfileJet_curvature_pos (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) _ _ _
  have hh := hnum.div (hden.const_mul 2) (mul_pos (by norm_num) (pow_pos hp 3)).ne'
  change Tendsto (fun q => (scalarPlantedJetPower hT α 2 2 q/q)/
    (2*scalarPlantedJetPower hT α 1 3 q)) (𝓝[>] 0)
    (𝓝 (scalarInitialDensityConstant hT α)) at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hQ)] with q hq hqQ
  rw [scalarSupport_cdf_ratio hT α hQ1 hc hs hmar ⟨hq,hqQ⟩]
  ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set Scalar
open scoped Topology NNReal

noncomputable def scalarQuantile (α : boundedMassProfiles) (u : ℝ) : ℝ :=
  sInf {x : ℝ | u ≤ profileStieltjes α x}

theorem scalarQuantile_level_nonempty {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {u : ℝ} (hu : u ≤ 1) : {x : ℝ | u ≤ profileStieltjes α x}.Nonempty := by
  refine ⟨1,?_⟩
  change u ≤ profileStieltjes α 1
  rwa [profileStieltjes_one hα]

theorem scalarQuantile_level_nonneg {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {u x : ℝ} (hu : 0 < u) (hx : u ≤ profileStieltjes α x) : 0 ≤ x := by
  by_contra hn
  have hh : profileStieltjes α x=0 := (rightMassProfile_mem hα).1 x (lt_of_not_ge hn)
  rw [hh] at hx
  exact (not_le_of_gt hu) hx

theorem scalarQuantile_level_bddBelow {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {u : ℝ} (hu : 0 < u) : BddBelow {x : ℝ | u ≤ profileStieltjes α x} :=
  ⟨0,fun _ hx => scalarQuantile_level_nonneg hα hu hx⟩

theorem scalarQuantile_cdf_ge {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) : u ≤ profileStieltjes α (scalarQuantile α u) := by
  let S := {x : ℝ | u ≤ profileStieltjes α x}
  have hn : S.Nonempty := scalarQuantile_level_nonempty hα hu.2
  have hb : BddBelow S := scalarQuantile_level_bddBelow hα hu.1
  have hc : ContinuousWithinAt (profileStieltjes α) S (sInf S) :=
    (profileStieltjes α).right_continuous (sInf S) |>.mono (fun _ hx => csInf_le hb hx)
  have he := MonotoneOn.map_csInf_of_continuousWithinAt hc
    ((profileStieltjes α).mono.monotoneOn S) hn hb
  change u ≤ profileStieltjes α (sInf S)
  rw [he]
  apply le_csInf (hn.image _)
  rintro _ ⟨x,hx,rfl⟩
  exact hx

theorem scalarQuantile_le_iff {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {u x : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    scalarQuantile α u ≤ x ↔ u ≤ profileStieltjes α x := by
  constructor
  · intro hx
    exact (scalarQuantile_cdf_ge hα hu).trans ((profileStieltjes α).mono hx)
  · exact csInf_le (scalarQuantile_level_bddBelow hα hu.1)

theorem scalarQuantile_nonneg {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) : 0 ≤ scalarQuantile α u :=
  le_csInf (scalarQuantile_level_nonempty hα hu.2)
    (fun _ hx => scalarQuantile_level_nonneg hα hu.1 hx)

theorem scalarQuantile_monotoneOn {α : boundedMassProfiles} (hα : α ∈ scalarProfiles) :
    MonotoneOn (scalarQuantile α) (Ioc (0:ℝ) 1) := by
  intro u hu v hv huv
  exact (scalarQuantile_le_iff hα hu).mpr (huv.trans (scalarQuantile_cdf_ge hα hv))

theorem scalarQuantile_pos {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    (hz : profileStieltjes α 0=0) {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    0 < scalarQuantile α u := by
  by_contra hn
  have hh := (scalarQuantile_le_iff hα hu).mp (le_of_not_gt hn)
  rw [hz] at hh
  exact (not_le_of_gt hu.1) hh

theorem scalarQuantile_le_support_top {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {q u : ℝ} (hs : (profileStieltjes α).measure.support=Icc 0 q) (hu : u ∈ Ioc (0:ℝ) 1) :
    scalarQuantile α u ≤ q := by
  apply (scalarQuantile_le_iff hα hu).mpr
  rw [scalarProfile_cdf_top hα hs]
  exact hu.2

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set Scalar
open scoped Topology NNReal

theorem scalarQuantile_continuousOn {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {q : ℝ} (hs : (profileStieltjes α).measure.support=Icc 0 q) :
    ContinuousOn (scalarQuantile α) (Ioo (0:ℝ) 1) := by
  intro u hu
  have hu' : u ∈ Ioc (0:ℝ) 1 := ⟨hu.1,hu.2.le⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let a := scalarQuantile α u-ε/2
  let b := scalarQuantile α u+ε/2
  have hqa : a < scalarQuantile α u := by dsimp only [a]; linarith
  have hqb : scalarQuantile α u < b := by dsimp only [b]; linarith
  have ha : profileStieltjes α a < u := by
    by_contra hh
    exact (not_le_of_gt hqa) ((scalarQuantile_le_iff hα hu').mpr (le_of_not_gt hh))
  have hb : u < profileStieltjes α b := by
    obtain hbt | hbt := le_total b q
    · exact (scalarQuantile_cdf_ge hα hu').trans_lt
        (scalarProfile_cdf_strictMono hs
          ⟨scalarQuantile_nonneg hα hu',scalarQuantile_le_support_top hα hs hu'⟩
          ⟨(scalarQuantile_nonneg hα hu').trans hqb.le,hbt⟩ hqb)
    · have hbb := (profileStieltjes α).mono hbt
      rw [scalarProfile_cdf_top hα hs] at hbb
      exact hu.2.trans_le hbb
  let δ := min (u-profileStieltjes α a) (profileStieltjes α b-u)/2
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)) (by norm_num)
  have hδa : δ ≤ (u-profileStieltjes α a)/2 := by
    dsimp only [δ]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδb : δ ≤ (profileStieltjes α b-u)/2 := by
    dsimp only [δ]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  refine ⟨δ,hδ,?_⟩
  intro v hv hd
  have hd' := abs_lt.mp (show |v-u|<δ by simpa only [Real.dist_eq] using hd)
  have hva : profileStieltjes α a < v := by linarith
  have hvb : v ≤ profileStieltjes α b := by linarith
  have hav : a < scalarQuantile α v := by
    by_contra hn
    exact (not_le_of_gt hva) ((scalarQuantile_le_iff hα ⟨hv.1,hv.2.le⟩).mp (le_of_not_gt hn))
  have hvc : scalarQuantile α v ≤ b := (scalarQuantile_le_iff hα ⟨hv.1,hv.2.le⟩).mpr hvb
  rw [Real.dist_eq,abs_lt]
  dsimp only [a,b] at hav hvc
  constructor <;> linarith

theorem scalarMinimizer_quantile_regular {T : ℝ} (hT : 1 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles)
    (hmin : ∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
      scalarParisiValue (zero_lt_one.trans hT) β) :
    ContinuousOn (scalarQuantile α) (Ioo (0:ℝ) 1) ∧
      MonotoneOn (scalarQuantile α) (Ioc (0:ℝ) 1) ∧
      ∀ u ∈ Ioo (0:ℝ) 1, scalarQuantile α u ∈ Ioo (0:ℝ) 1 := by
  obtain ⟨q,hq,hs⟩ := scalarMinimizer_support_eq_initial_interval hT α hα hmin
  refine ⟨scalarQuantile_continuousOn hα hs,scalarQuantile_monotoneOn hα,?_⟩
  intro u hu
  exact ⟨scalarQuantile_pos hα (scalarMinimizer_cdf_zero hT α hα hmin) ⟨hu.1,hu.2.le⟩,
    (scalarQuantile_le_support_top hα hs ⟨hu.1,hu.2.le⟩).trans_lt hq.2⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set Scalar
open scoped Topology NNReal

theorem scalarParisiValue_attains_regular_support {T : ℝ} (hT : 1 < T) :
    ∃ (α : boundedMassProfiles) (q : ℝ), α ∈ scalarProfiles ∧ q ∈ Ioo (0:ℝ) 1 ∧
      (∀ s, ContinuousWithinAt α.val (Ici s) s) ∧
      IsProbabilityMeasure (profileStieltjes α).measure ∧
      (∀ s, cdf (profileStieltjes α).measure s=α.val s) ∧
      (∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
        scalarParisiValue (zero_lt_one.trans hT) β) ∧
      (profileStieltjes α).measure.support=Icc 0 q ∧
      (profileStieltjes α).measure {(0:ℝ)}=0 ∧ α.val 0=0 ∧
      (∀ s ∈ Icc 0 q, scalarPlantedEnergy (zero_lt_one.trans hT) α s=s) ∧
      (∀ s ∈ Icc 0 q, T*scalarPlantedCurvature (zero_lt_one.trans hT) α s=1) ∧
      (∀ s ∈ Ioo 0 q, ContinuousAt α.val s) ∧
      (∀ s ∈ Ioo 0 q, α.val s=scalarPlantedJetPower (zero_lt_one.trans hT) α 2 2 s /
        (2*scalarPlantedJetPower (zero_lt_one.trans hT) α 1 3 s)) ∧
      ContinuousOn (scalarQuantile α) (Ioo (0:ℝ) 1) := by
  obtain ⟨α,q,hα,hq,hc,hp,hcdf,hmin,hs,hno,hzero,hΓ,_hm⟩ :=
    scalarParisiValue_attains_interval_support hT
  have hmar := scalarSupport_curvature_marginality (zero_lt_one.trans hT) α hq.1 hq.2 hc hs hΓ
  exact ⟨α,q,hα,hq,hc,hp,hcdf,hmin,hs,hno,hzero,hΓ,hmar,
    fun _ hx => scalarSupport_cdf_continuousAt (zero_lt_one.trans hT) α hq.2 hc hs hmar hx,
    fun _ hx => scalarSupport_cdf_ratio (zero_lt_one.trans hT) α hq.2 hc hs hmar hx,
    scalarQuantile_continuousOn hα hs⟩

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set Scalar
open scoped Topology NNReal

theorem profileStieltjes_eq_of_rightContinuous (α : boundedMassProfiles)
    (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x) :
    (profileStieltjes α : ℝ → ℝ)=α.val := by
  funext x
  exact (hc x).rightLim_eq

theorem scalarQuantile_cdf_eq {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1)
    (hc : ContinuousAt (profileStieltjes α) (scalarQuantile α u)) :
    profileStieltjes α (scalarQuantile α u)=u := by
  apply le_antisymm _ (scalarQuantile_cdf_ge hα hu)
  apply le_of_not_gt
  intro hlt
  have he : ∀ᶠ x in 𝓝[<] (scalarQuantile α u), u < profileStieltjes α x :=
    (hc.tendsto.mono_left nhdsWithin_le_nhds).eventually (eventually_gt_nhds hlt)
  have hy : ∀ᶠ x in 𝓝[<] (scalarQuantile α u), x < scalarQuantile α u := self_mem_nhdsWithin
  obtain ⟨x,hx,hux⟩ := (hy.and he).exists
  exact (not_le_of_gt hx) ((scalarQuantile_le_iff hα hu).mpr hux.le)

theorem scalarQuantile_tendsto_zero {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {Q : ℝ} (hQ : 0 < Q) (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x)
    (hs : (profileStieltjes α).measure.support=Icc 0 Q) :
    Tendsto (scalarQuantile α) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))]
      with u hu hu1
    exact ha.trans_le (scalarQuantile_nonneg hα ⟨hu,hu1.le⟩)
  · intro b hb
    let x := min (b/2) (Q/2)
    have hx : 0 < x := lt_min (half_pos hb) (half_pos hQ)
    have hxQ : x ≤ Q := (min_le_right _ _).trans (by linarith)
    have hxb : x < b := (min_le_left _ _).trans_lt (by linarith)
    have hp : 0 < profileStieltjes α x := by
      rw [profileStieltjes_eq_of_rightContinuous α hc]
      exact scalarSupport_cdf_positive α hc hs ⟨hx,hxQ⟩
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hp),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))]
      with u hu hux hu1
    exact ((scalarQuantile_le_iff hα ⟨hu,hu1.le⟩).mpr hux.le).trans_lt hxb

theorem scalarQuantile_tendsto_zero_right {α : boundedMassProfiles} (hα : α ∈ scalarProfiles)
    {Q : ℝ} (hQ : 0 < Q) (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x)
    (hs : (profileStieltjes α).measure.support=Icc 0 Q) (hz : α.val 0=0) :
    Tendsto (scalarQuantile α) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨scalarQuantile_tendsto_zero hα hQ hc hs,?_⟩
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))]
    with u hu hu1
  apply scalarQuantile_pos hα _ ⟨hu,hu1.le⟩
  rw [profileStieltjes_eq_of_rightContinuous α hc,hz]

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal

theorem scalarSupport_quantile_initial_limit {T Q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles) (hQ : 0 < Q) (hQ1 : Q < 1)
    (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x) (hz : α.val 0=0)
    (hs : (profileStieltjes α).measure.support=Icc 0 Q)
    (hmar : ∀ x ∈ Icc 0 Q, T*scalarPlantedCurvature hT α x=1) :
    Tendsto (fun u => scalarQuantile α u/u) (𝓝[>] 0)
      (𝓝 (1/scalarInitialDensityConstant hT α)) := by
  have ht := scalarQuantile_tendsto_zero_right hα hQ hc hs hz
  have hd := (scalarSupport_cdf_initial_limit hT α hQ hQ1 hc hs hmar).comp ht
  have hh := (tendsto_const_nhds (x:=(1:ℝ))).div hd (scalarInitialDensityConstant_pos hT α).ne'
  apply hh.congr'
  have hlt : ∀ᶠ u in 𝓝[>] 0, scalarQuantile α u < Q :=
    (scalarQuantile_tendsto_zero hα hQ hc hs).eventually (eventually_lt_nhds hQ)
  filter_upwards [self_mem_nhdsWithin,hlt,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))]
    with u hu huQ hu1
  have hp := scalarQuantile_pos hα (show profileStieltjes α 0=0 by
    rw [profileStieltjes_eq_of_rightContinuous α hc,hz]) ⟨hu,hu1.le⟩
  have he : α.val (scalarQuantile α u)=u := by
    rw [← profileStieltjes_eq_of_rightContinuous α hc]
    apply scalarQuantile_cdf_eq hα ⟨hu,hu1.le⟩
    rw [profileStieltjes_eq_of_rightContinuous α hc]
    exact scalarSupport_cdf_continuousAt hT α hQ1 hc hs hmar ⟨hp,huQ⟩
  change 1/(α.val (scalarQuantile α u)/scalarQuantile α u)=scalarQuantile α u/u
  rw [he,one_div_div]

theorem scalarSupport_quantile_linear_bounds {T Q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hα : α ∈ scalarProfiles) (hQ : 0 < Q) (hQ1 : Q < 1)
    (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x) (hz : α.val 0=0)
    (hs : (profileStieltjes α).measure.support=Icc 0 Q)
    (hmar : ∀ x ∈ Icc 0 Q, T*scalarPlantedCurvature hT α x=1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u ∈ Ioo (0:ℝ) 1,
      c*u ≤ scalarQuantile α u ∧ scalarQuantile α u ≤ C*u := by
  apply monotone_initial_ratio_uniform_bounds
    (one_div_pos.mpr (scalarInitialDensityConstant_pos hT α))
    (scalarSupport_quantile_initial_limit hT α hα hQ hQ1 hc hz hs hmar)
    (scalarQuantile_monotoneOn hα)
  · intro u hu
    apply scalarQuantile_pos hα _ ⟨hu.1,hu.2.le⟩
    rw [profileStieltjes_eq_of_rightContinuous α hc,hz]
  · intro u hu
    exact (scalarQuantile_le_support_top hα hs ⟨hu.1,hu.2.le⟩).trans hQ1.le

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set Scalar
open scoped Topology NNReal

theorem scalarParisiValue_attains_linear_quantile {T : ℝ} (hT : 1 < T) :
    ∃ (α : boundedMassProfiles) (q : ℝ), α ∈ scalarProfiles ∧ q ∈ Ioo (0:ℝ) 1 ∧
      (∀ s, ContinuousWithinAt α.val (Ici s) s) ∧
      IsProbabilityMeasure (profileStieltjes α).measure ∧
      (∀ s, cdf (profileStieltjes α).measure s=α.val s) ∧
      (∀ β ∈ scalarProfiles, scalarParisiValue (zero_lt_one.trans hT) α ≤
        scalarParisiValue (zero_lt_one.trans hT) β) ∧
      (profileStieltjes α).measure.support=Icc 0 q ∧
      (profileStieltjes α).measure {(0:ℝ)}=0 ∧ α.val 0=0 ∧
      (∀ s ∈ Icc 0 q, scalarPlantedEnergy (zero_lt_one.trans hT) α s=s) ∧
      (∀ s ∈ Icc 0 q, T*scalarPlantedCurvature (zero_lt_one.trans hT) α s=1) ∧
      (∀ s ∈ Ioo 0 q, ContinuousAt α.val s) ∧
      (∀ s ∈ Ioo 0 q, α.val s=scalarPlantedJetPower (zero_lt_one.trans hT) α 2 2 s /
        (2*scalarPlantedJetPower (zero_lt_one.trans hT) α 1 3 s)) ∧
      ContinuousOn (scalarQuantile α) (Ioo (0:ℝ) 1) ∧
      0 < scalarInitialDensityConstant (zero_lt_one.trans hT) α ∧
      Tendsto (fun s => α.val s/s) (𝓝[>] 0)
        (𝓝 (scalarInitialDensityConstant (zero_lt_one.trans hT) α)) ∧
      Tendsto (fun u => scalarQuantile α u/u) (𝓝[>] 0)
        (𝓝 (1/scalarInitialDensityConstant (zero_lt_one.trans hT) α)) ∧
      (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u ∈ Ioo (0:ℝ) 1,
        c*u ≤ scalarQuantile α u ∧ scalarQuantile α u ≤ C*u) := by
  obtain ⟨α,q,hα,hq,hc,hp,hcdf,hmin,hs,hno,hzero,hΓ,hmar,hcont,hratio,hquant⟩ :=
    scalarParisiValue_attains_regular_support hT
  exact ⟨α,q,hα,hq,hc,hp,hcdf,hmin,hs,hno,hzero,hΓ,hmar,hcont,hratio,hquant,
    scalarInitialDensityConstant_pos (zero_lt_one.trans hT) α,
    scalarSupport_cdf_initial_limit (zero_lt_one.trans hT) α hq.1 hq.2 hc hs hmar,
    scalarSupport_quantile_initial_limit (zero_lt_one.trans hT) α hα hq.1 hq.2 hc hzero hs hmar,
    scalarSupport_quantile_linear_bounds (zero_lt_one.trans hT) α hα hq.1 hq.2 hc hzero hs hmar⟩

end SKFluctuations.Hierarchy

end

end OAI
