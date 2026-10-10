import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.PlanarGrid
import OAI.Probability.SLEGauge.NormalizedDiskMass

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart PastMass CompactSequence

lemma half_le_subdiskRadius (n : ℕ) : (1:ℝ)/2 ≤ subdiskRadius n := by
  unfold subdiskRadius
  have h : (2:ℝ) ≤ n+2 := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
  have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) h
  linarith

lemma radial_exp_tendsto (a : ℝ) (ha : 0<a) :
    Tendsto (fun l : ℕ=>Real.exp (-2*a*l)) atTop (𝓝 0) := by
  have H := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-2*a)).le
    (Real.exp_lt_one_iff.mpr (by linarith : -2*a<0))
  simpa only [←Real.exp_nat_mul, mul_comm (↑_ : ℝ) (-2*a)] using H

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4<a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

 

lemma finite_past_tail [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (z : UpperPlane) (σ : ℝ) (hσ : 0<σ) (hσz : σ ≤ z.1.im)
    (s : ℝ) (hs : Jacobi.mixingTime (4*a) ≤ s) (hgap : σ=z.1.im*Real.exp (-2*a*s))
    (Q : Set UpperPlane) (hQ : Q ⊆ (Subtype.val : UpperPlane→ℂ) ⁻¹' closedBall z.1 (σ/200))
    (F : Finset ℝ≥0) (H : ℝ) (hH : 0 ≤ H) (l : ℕ) :
    (radialLaw W a z.1 (σ*Real.exp (-2*a*l)))
      {b | finiteTestTime F (fun t b=>M.mass t b Q)
        (ENNReal.ofReal (((diskUpper (subdiskRadius M.radiusIndex)*σ)^(2-alpha a))*H)) b <
          radialTime a b.1 z.1 (σ*Real.exp (-2*a*l))} ≤
      2*M.law {x | H ≤ sequenceMassReal x} := by
  let q := subdiskRadius M.radiusIndex
  have hq : 0 ≤ q := (subdiskRadius_pos _).le
  have hq1 : q<1 := subdiskRadius_lt_one _
  have ha0 : 0<a := by linarith
  have hρ : 0<σ*Real.exp (-2*a*l) := mul_pos hσ (Real.exp_pos _)
  have hρσ : σ*Real.exp (-2*a*l) ≤ σ := mul_le_of_le_one_right hσ.le
    (Real.exp_le_one_iff.mpr (by have := Nat.cast_nonneg (α:=ℝ) l; nlinarith))
  have hac : radialLaw W a z.1 (σ*Real.exp (-2*a*l)) ≪ W :=
    withDensity_absolutelyContinuous _ _
  have hbound := actual_radial_spatial_bounds κ a ha W M.supports M.coeff M.nonneg
    M.canonical z.1 z.2 σ hσ hσz q hq hq1
  refine le_trans ?_ (M.normalized_tail_le hW z.1 z.2 σ hσ hσz s hs hgap l H hH)
  apply measure_mono_ae
  filter_upwards [hac.ae_le M.canonical.path,hac.ae_le hbound,
    radial_hit_ae W a ha z.1 z.2 _ hρ (hρσ.trans hσz)] with b hb hbb hhit
  intro hbf
  have hS : radialTime a b.1 z.1 σ≠∞ := ne_top_of_le_ne_top hhit
    (radialTime_antitone a ha0 z.1 z.2 _ σ hρ hρσ hσz b)
  have hloc := (radialDiskRegion_localization a ha0 z.1 z.2 σ hσ hσz
    (half_le_subdiskRadius M.radiusIndex) hq1 b hS).1
  obtain ⟨t,ht,htmass,htT⟩ := (finiteTestTime_lt_iff _ _ _ _ _).mp hbf
  have hmass := (htmass.trans_le (hb.monotone htT.le Q)).trans_le
    ((measure_mono (hQ.trans hloc)).trans ((hbb hS).2 l).2)
  have hpos : 0<(diskUpper q*σ)^(2-alpha a) := Real.rpow_pos_of_pos
    (mul_pos (diskUpper_pos hq hq1) hσ) _
  rw [ENNReal.ofReal_mul hpos.le] at hmass
  exact ((ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr hpos).ne'
    ENNReal.ofReal_ne_top).mp hmass).le

 
lemma past_kernel_tail [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (z : UpperPlane) (σ : ℝ) (hσ : 0<σ) (hσz : σ ≤ z.1.im)
    (s : ℝ) (hs : Jacobi.mixingTime (4*a) ≤ s) (hgap : σ=z.1.im*Real.exp (-2*a*s))
    (Q : Set UpperPlane) (hQm : MeasurableSet Q)
    (hQ : Q ⊆ (Subtype.val : UpperPlane→ℂ) ⁻¹' closedBall z.1 (σ/200))
    (F : Finset ℝ≥0) (H : ℝ) (hH : 0 ≤ H) :
    pastGreenKernel W a (finiteTestTime F (fun t b=>M.mass t b Q)
      (ENNReal.ofReal (((diskUpper (subdiskRadius M.radiusIndex)*σ)^(2-alpha a))*H))) z ≤
      2*M.law {x | H ≤ sequenceMassReal x} := by
  let ratio (l : ℕ) := (σ/z.1.im)*Real.exp (-2*a*l)
  have hr (l : ℕ) : 0<ratio l ∧ ratio l ≤ 1 := by
    refine ⟨mul_pos (div_pos hσ z.2) (Real.exp_pos _),?_⟩
    exact (mul_le_of_le_one_right (div_pos hσ z.2).le
      (Real.exp_le_one_iff.mpr (by have := Nat.cast_nonneg (α:=ℝ) l; nlinarith))).trans
      ((div_le_one z.2).mpr hσz)
  have hr0 : Tendsto ratio atTop (𝓝 0) := by
    simpa only [mul_zero] using (radial_exp_tendsto a (by linarith)).const_mul (σ/z.1.im)
  have e (l : ℕ) : z.1.im*ratio l=σ*Real.exp (-2*a*l) := by
    dsimp only [ratio]
    field_simp [z.2.ne']
  have ht := radialLaw_strict_past_tendsto W hW a ha _
    (M.canonical.toTracePalmData.test_stopping Q hQm F
      (ENNReal.ofReal (((diskUpper (subdiskRadius M.radiusIndex)*σ)^(2-alpha a))*H))) z ratio hr hr0
  simp only [e] at ht
  exact le_of_tendsto ht (Eventually.of_forall (fun l=>
    M.finite_past_tail hW z σ hσ hσz s hs hgap Q hQ F H hH l))

lemma rational_past_kernel_tail [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (z : UpperPlane) (σ : ℝ) (hσ : 0<σ) (hσz : σ ≤ z.1.im)
    (s : ℝ) (hs : Jacobi.mixingTime (4*a) ≤ s) (hgap : σ=z.1.im*Real.exp (-2*a*s))
    (Q : Set UpperPlane) (hQm : MeasurableSet Q)
    (hQ : Q ⊆ (Subtype.val : UpperPlane→ℂ) ⁻¹' closedBall z.1 (σ/200))
    (H : ℝ) (hH : 0 ≤ H) :
    rationalPastKernel W a M.mass Q
      (ENNReal.ofReal (((diskUpper (subdiskRadius M.radiusIndex)*σ)^(2-alpha a))*H)) z ≤
      2*M.law {x | H ≤ sequenceMassReal x} := by
  apply iSup_le
  intro n
  exact M.past_kernel_tail hW z σ hσ hσz s hs hgap Q hQm hQ _ H hH

 

lemma expected_spatial_bad_mass [IsProbabilityMeasure W]
    (hκ : 0<κ) (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (σ : ℝ) (hσ : 0<σ) (Q : Set UpperPlane) (hQ : IsCompact Q)
    (hsize : ∀z∈Q,Q ⊆ (Subtype.val : UpperPlane→ℂ) ⁻¹' closedBall z.1 (σ/200))
    (hgap : ∀z∈Q,σ ≤ z.1.im ∧ ∃s : ℝ,Jacobi.mixingTime (4*a) ≤ s ∧
      σ=z.1.im*Real.exp (-2*a*s))
    (H : ℝ) (hH : 0 ≤ H) :
    (∫⁻b,{b | 2*ENNReal.ofReal (((diskUpper (subdiskRadius M.radiusIndex)*σ)^(2-alpha a))*H)<
      M.mass ∞ b Q}.indicator (fun b=>M.mass ∞ b Q) b∂W) ≤
      4*initialGreenMeasure a Q*M.law {x | H ≤ sequenceMassReal x} := by
  have hh := M.canonical.toTracePalmData.expected_bad_mass_le hκ ha hW Q hQ
    (((diskUpper (subdiskRadius M.radiusIndex)*σ)^(2-alpha a))*H)
    (mul_nonneg (Real.rpow_nonneg (mul_nonneg
      (diskUpper_pos (subdiskRadius_pos _).le (subdiskRadius_lt_one _)).le hσ.le) _) hH)
  refine hh.trans ?_
  have hb : (∫⁻z in Q,ENNReal.ofReal (initialGreen a z)*rationalPastKernel W a M.mass Q
      (ENNReal.ofReal (((diskUpper (subdiskRadius M.radiusIndex)*σ)^(2-alpha a))*H)) z∂upperArea) ≤
      (initialGreenMeasure a Q)*(2*M.law {x | H ≤ sequenceMassReal x}) := by
    have hb' : (∫⁻z in Q,ENNReal.ofReal (initialGreen a z)*rationalPastKernel W a M.mass Q
      (ENNReal.ofReal (((diskUpper (subdiskRadius M.radiusIndex)*σ)^(2-alpha a))*H)) z∂upperArea) ≤
      ∫⁻z in Q,ENNReal.ofReal (initialGreen a z)*(2*M.law {x | H ≤ sequenceMassReal x})∂upperArea := by
      apply setLIntegral_mono' hQ.measurableSet
      intro z hz
      gcongr
      obtain ⟨hsz,s,hs,he⟩ := hgap z hz
      exact M.rational_past_kernel_tail hW z σ hσ hsz s hs he Q hQ.measurableSet
        (hsize z hz) H hH
    refine hb'.trans_eq ?_
    rw [lintegral_mul_const _ (initialGreen_continuous a).measurable.ennreal_ofReal]
    rw [initialGreenMeasure,withDensity_apply _ hQ.measurableSet]
  calc
    _ ≤ 2*(initialGreenMeasure a Q*(2*M.law {x | H ≤ sequenceMassReal x})) := by gcongr; exact hb
    _ = _ := by ring

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart PastMass CompactSequence MomentBatches

lemma clock_gap_of_small (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : 0 ≤ T)
    (y σ : ℝ) (hy : 0 < y) (hσ : 0 < σ) (hsmall : σ ≤ y*Real.exp (-2*a*T)) :
    σ ≤ y ∧ ∃s : ℝ,T ≤ s ∧ σ=y*Real.exp (-2*a*s) := by
  have hq := div_pos hσ hy
  have he : σ/y ≤ Real.exp (-2*a*T) := (div_le_iff₀ hy).mpr (by simpa only [mul_comm] using hsmall)
  have hlog := Real.log_le_log hq he
  rw [Real.log_exp] at hlog
  have hσy : σ ≤ y := hsmall.trans (mul_le_of_le_one_right hy.le
    (Real.exp_le_one_iff.mpr (by nlinarith)))
  refine ⟨hσy,-Real.log (σ/y)/(2*a),?_,?_⟩
  · apply (le_div_iff₀ (by positivity : 0 < 2*a)).mpr
    nlinarith
  · have ee : -2*a*(-Real.log (σ/y)/(2*a))=Real.log (σ/y) := by field_simp
    rw [ee,Real.exp_log hq,mul_div_cancel₀ _ hy.ne']

lemma batchRadius_eventually_small (m : ℕ → ℝ) (a : ℝ) (ha : 0 ≤ a) (ell : ℕ → ℕ)
    (ε : ℝ) (hε : 0 < ε) : ∃N : ℕ,∀i : EntryIndex m,N ≤ i.1.1 → radius m a ell i ≤ ε := by
  have ht : Tendsto (fun n : ℕ=>Real.exp (-(n:ℝ))) atTop (𝓝 0) := by
    simpa using radial_exp_tendsto (1/2) (by norm_num : (0:ℝ) < 1/2)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually_le_const hε)
  refine ⟨N,fun i hi=>(radius_le m ha ell i).trans ((Real.exp_le_exp.mpr ?_).trans (hN i.1.1 hi))⟩
  have hn : (1:ℝ) ≤ i.1.1 := by exact_mod_cast i.1.2
  nlinarith

lemma compact_batch_mixing (m : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (ell : ℕ → ℕ)
    (E : Set UpperPlane) (hE : IsCompact E) :
    ∃N : ℕ,∀i : EntryIndex m,N ≤ i.1.1 → ∀z∈E,
      400*radius m a ell i ≤ z.1.im ∧ ∃s : ℝ,Jacobi.mixingTime (4*a) ≤ s ∧
        400*radius m a ell i=z.1.im*Real.exp (-2*a*s) := by
  obtain ⟨η,hη,hηE⟩ := hE.exists_forall_le'
    (Complex.continuous_im.comp continuous_subtype_val).continuousOn (fun z _=>z.2)
  let T := Jacobi.mixingTime (4*a)
  have hT : 0 ≤ T := by unfold T Jacobi.mixingTime Jacobi.majorantBase; positivity
  obtain ⟨N,hN⟩ := batchRadius_eventually_small m a ha.le ell
    (η*Real.exp (-2*a*T)/400) (by positivity)
  refine ⟨N,fun i hi z hz=>clock_gap_of_small a ha T hT z.1.im
    (400*radius m a ell i) z.2 (by have := radius_pos m a ell i; positivity) ?_⟩
  calc
    400*radius m a ell i ≤ η*Real.exp (-2*a*T) := by linarith [hN i hi]
    _ ≤ z.1.im*Real.exp (-2*a*T) := mul_le_mul_of_nonneg_right (hηE z hz) (Real.exp_pos _).le

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4 < a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

abbrev Entries := EntryIndex (moment M.law sequenceMassReal)

def entryThreshold (i : M.Entries) : ℝ := threshold (moment M.law sequenceMassReal) i

def entryRadius (i : M.Entries) : ℝ := radius (moment M.law sequenceMassReal) a
  (momentLevel M.law sequenceMassReal sequenceLevelReal) i

lemma entryRadius_pos (i : M.Entries) : 0 < M.entryRadius i := radius_pos ..

lemma entryThreshold_pos (i : M.Entries) : 0 < M.entryThreshold i := by
  let := M.probability
  have hm1 := M.moments_positive 1 le_rfl
  have hh := batch_entry_lower i.1.2 hm1 (M.moments_positive i.1.1 i.1.2)
    (mean_pow_le_moment M.law sequenceMassReal
      (Eventually.of_forall sequenceMassReal_nonneg) (by simpa only [pow_one] using M.integrable_moments 1) i.1.1 (M.integrable_moments _))
    (List.getElem_mem i.2.2)
  exact (lt_min zero_lt_one (by positivity : 0 < moment M.law sequenceMassReal 1/4)).trans_le hh

lemma gauge_eq_quadratic (d : ℝ) :
    M.gauge d=QuadraticGauge.gauge d M.entryThreshold M.entryRadius := rfl

lemma entry_tails_finite : (∑'i : M.Entries,
    M.law {x | 16*M.entryThreshold i ≤ sequenceMassReal x})≠∞ := by
  let := M.probability
  have h := M.tails_summable.tsum_ofReal_ne_top
  simpa only [entryThreshold,Entries,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.CenteredMoments
open ExactSLEGreen

 
def spatialRestriction (μ : Measure UpperPlane) (E : Set UpperPlane) : Measure ℂ :=
  (μ.restrict E).map Subtype.val

lemma spatialRestriction_apply (μ : Measure UpperPlane) (E : Set UpperPlane)
    (A : Set ℂ) (hA : MeasurableSet A) :
    spatialRestriction μ E A=μ (E∩(Subtype.val : UpperPlane→ℂ) ⁻¹' A) := by
  rw [spatialRestriction,Measure.map_apply measurable_subtype_coe hA,
    Measure.restrict_apply (measurable_subtype_coe hA),inter_comm]

lemma spatialRestriction_mono {μ ν : Measure UpperPlane} (h : μ≤ν) (E : Set UpperPlane) :
    spatialRestriction μ E ≤ spatialRestriction ν E := by
  exact Measure.map_mono (Measure.restrict_mono le_rfl h) measurable_subtype_coe

lemma spatialRestriction_univ (μ : Measure UpperPlane) (E : Set UpperPlane) :
    spatialRestriction μ E univ=μ E := by
  rw [spatialRestriction_apply μ E univ MeasurableSet.univ]
  simp

lemma spatialRestriction_finite (μ : Measure UpperPlane) (E : Set UpperPlane) (hE : μ E<∞) :
    IsFiniteMeasure (spatialRestriction μ E) :=
  ⟨by simpa only [spatialRestriction_univ] using hE⟩

lemma spatialRestriction_atomless (μ : Measure UpperPlane) [NullSingletonClass μ]
    (E : Set UpperPlane) : NullSingletonClass (spatialRestriction μ E) := by
  constructor
  intro z
  rw [spatialRestriction_apply μ E {z} (measurableSet_singleton z)]
  exact measure_mono_null inter_subset_right
    ((Set.subsingleton_singleton.preimage Subtype.val_injective).measure_zero μ)

lemma spatialRestriction_measurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω→Measure UpperPlane) (hμ : Measurable μ) (E : Set UpperPlane)
    (hE : MeasurableSet E) (A : Set ℂ) (hA : MeasurableSet A) :
    Measurable (fun ω=>spatialRestriction (μ ω) E A) := by
  simp only [spatialRestriction_apply _ _ _ hA]
  exact (Measure.measurable_coe (hE.inter (measurable_subtype_coe hA))).comp hμ

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart PastMass CompactSequence MomentBatches

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4<a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

def gridConstant : ℝ := 32*(400*diskUpper (subdiskRadius M.radiusIndex))^(2-alpha a)

lemma gridConstant_pos : 0 < M.gridConstant := by
  have hU := diskUpper_pos (subdiskRadius_pos M.radiusIndex).le (subdiskRadius_lt_one M.radiusIndex)
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)

lemma grid_threshold (i : M.Entries) :
    2*ENNReal.ofReal (((diskUpper (subdiskRadius M.radiusIndex)*(400*M.entryRadius i))^(2-alpha a))*(16*M.entryThreshold i))=
      ENNReal.ofReal (M.gridConstant*M.entryThreshold i*(M.entryRadius i)^(2-alpha a)) := by
  have hU := diskUpper_pos (subdiskRadius_pos M.radiusIndex).le (subdiskRadius_lt_one M.radiusIndex)
  have he : diskUpper (subdiskRadius M.radiusIndex)*(400*M.entryRadius i)=
      (400*diskUpper (subdiskRadius M.radiusIndex))*M.entryRadius i := by ring
  rw [he, Real.mul_rpow (by positivity : 0 ≤ 400*diskUpper (subdiskRadius M.radiusIndex))
    (M.entryRadius_pos i).le,←ENNReal.ofReal_ofNat (n:=2),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  unfold gridConstant
  ring

 

theorem compact_finitely_bad [IsProbabilityMeasure W]
    (hκ : 0<κ) (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (E : Set UpperPlane) (hE : IsCompact E) :
    ∀ᵐ b∂W,∀ᵐ z∂spatialRestriction (M.mass ∞ b) E,
      {i : M.Entries | z∈PlanarGrid.badRegion (spatialRestriction (M.mass ∞ b) E)
        (M.entryRadius i) (M.gridConstant*M.entryThreshold i*(M.entryRadius i)^(2-alpha a))}.Finite := by
  let ν := spatialRestriction (initialGreenMeasure a) E
  let : IsFiniteMeasure ν := spatialRestriction_finite _ E hE.measure_lt_top
  obtain ⟨N,hN⟩ := compact_batch_mixing (moment M.law sequenceMassReal) a (by linarith)
    (momentLevel M.law sequenceMassReal sequenceLevelReal) E hE
  let good : Set M.Entries := {i | N ≤ i.1.1}
  have hg : goodᶜ.Finite := by
    simpa only [good,compl_ofPred,not_le] using finite_entries_before (moment M.law sequenceMassReal) N
  apply PlanarGrid.ae_finitely_bad_of_spatial_tails W
    (fun b=>spatialRestriction (M.mass ∞ b) E) ν M.entryRadius
    (fun i=>M.gridConstant*M.entryThreshold i*(M.entryRadius i)^(2-alpha a)) M.entryRadius_pos
    (fun i p=>spatialRestriction_measurable (M.mass ∞) M.canonical.terminal_measurable E
      hE.measurableSet _ (PlanarGrid.cell_measurable _ _)) good hg 4 (by norm_num)
    (fun i=>M.law {x | 16*M.entryThreshold i ≤ sequenceMassReal x}) M.entry_tails_finite
  intro i hi p
  let Q := E∩(Subtype.val : UpperPlane→ℂ) ⁻¹' PlanarGrid.cell (M.entryRadius i) p
  have hQ : IsCompact Q := hE.inter_right
    ((PlanarGrid.cell_closed _ _).preimage continuous_subtype_val)
  have hs : ∀z∈Q,Q ⊆ (Subtype.val : UpperPlane→ℂ) ⁻¹' closedBall z.1 ((400*M.entryRadius i)/200) := by
    intro z hz w hw
    apply mem_closedBall.mpr
    calc
      dist w.1 z.1 ≤ 2*M.entryRadius i := PlanarGrid.cell_dist _ (M.entryRadius_pos i).le p hz.2 hw.2
      _ = (400*M.entryRadius i)/200 := by ring
  have hh := M.expected_spatial_bad_mass hκ hW (400*M.entryRadius i)
    (by have := M.entryRadius_pos i; positivity) Q hQ hs
    (fun z hz=>hN i hi z hz.1) (16*M.entryThreshold i) (by have := M.entryThreshold_pos i; positivity)
  rw [M.grid_threshold] at hh
  simpa only [ν,spatialRestriction_apply _ _ _ (PlanarGrid.cell_measurable _ _)] using hh

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart PastMass CompactSequence MomentBatches TraceMassContinuity

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4<a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

 

theorem hausdorff_positive [IsProbabilityMeasure W]
    (hκ : 0<κ) (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W) :
    ∀ᵐ b∂W,∀s t : ℝ,0<s → s<t →
      0<Target.hausdorff (M.gauge (2-alpha a))
        ((Target.trace κ (driverHomeomorph.symm b)) '' Icc s t) := by
  let E := CompactExhaustion.choice UpperPlane
  have hbad : ∀ᵐ b∂W,∀n : ℕ,∀ᵐ z∂spatialRestriction (M.mass ∞ b) (E n),
      {i : M.Entries | z∈PlanarGrid.badRegion (spatialRestriction (M.mass ∞ b) (E n))
        (M.entryRadius i) (M.gridConstant*M.entryThreshold i*(M.entryRadius i)^(2-alpha a))}.Finite :=
    ae_all_iff.mpr (fun n=>M.compact_finitely_bad hκ hW (E n) (E.isCompact n))
  filter_upwards [hbad,M.canonical.path,M.canonical.positive_increments] with b hb hf hp
  intro s t hs hst
  let u := (κ*s).toNNReal
  let v := (κ*t).toNNReal
  have hu : (u:ℝ)=κ*s := Real.coe_toNNReal _ (mul_pos hκ hs).le
  have hv : (v:ℝ)=κ*t := Real.coe_toNNReal _ (mul_pos hκ (hs.trans hst)).le
  have huv : u<v := by
    change (u:ℝ)<(v:ℝ)
    rw [hu,hv]
    exact mul_lt_mul_of_pos_left hst hκ
  obtain ⟨_,K,hK,hKpos,_⟩ := hp u v huv
  obtain ⟨n,hKn⟩ := E.exists_superset_of_isCompact hK
  let τ := M.mass v b-M.mass u b
  have hτ : τ ≤ M.mass ∞ b := Measure.sub_le.trans (hf.monotone le_top)
  let : NullSingletonClass (M.mass ∞ b) := hf.atomless
  let : NullSingletonClass τ := ⟨fun z=>measure_mono_null (le_refl {z})
    (le_antisymm ((hτ {z}).trans_eq (measure_singleton z)) bot_le)⟩
  let : IsFiniteMeasureOnCompacts (M.mass ∞ b) := M.canonical.finite_compact ∞ b
  let σ := spatialRestriction τ (E n)
  let μ := spatialRestriction (M.mass ∞ b) (E n)
  have hσ : σ≤μ := spatialRestriction_mono hτ (E n)
  let : IsFiniteMeasure σ := spatialRestriction_finite τ (E n)
    ((hτ (E n)).trans_lt (E.isCompact n).measure_lt_top)
  let : NullSingletonClass σ := spatialRestriction_atomless τ (E n)
  let A : Set ℂ := (Target.trace κ (driverHomeomorph.symm b)) '' Icc s t
  have hA : IsCompact A := isCompact_Icc.image_of_continuousOn
    (hf.continuous_trace.mono (fun x hx=>hs.le.trans hx.1))
  have hzero : σ Aᶜ=0 := by
    rw [spatialRestriction_apply τ (E n) _ hA.measurableSet.compl]
    apply measure_mono_null inter_subset_right
    exact hf.capacity_increment_support hκ s t hs.le hst.le
  have hpos : 0<σ A := by
    have hposU : 0<σ univ := by
      rw [spatialRestriction_univ]
      exact hKpos.trans_le (measure_mono hKn)
    have he := measure_add_measure_compl (μ:=σ) hA.measurableSet
    rw [hzero,add_zero] at he
    exact he ▸ hposU
  rw [M.gauge_eq_quadratic]
  exact PlanarGrid.hausdorff_pos_of_finitely_bad (2-alpha a) M.entryThreshold M.entryRadius
    M.entryThreshold_pos M.entryRadius_pos μ σ hσ M.gridConstant M.gridConstant_pos.le
    ((Measure.absolutelyContinuous_of_le hσ).ae_le (hb n)) A hpos

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart PastMass CompactSequence MomentBatches

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4<a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

def stoppedTest (z : ℂ) (τ : ℝ) (l : ℕ) : GDriver→ℝ≥0∞ :=
  finiteStoppedTest (fun b : GDriver=>radialTime a b.1 z (τ*Real.exp (-2*a*l)))
    (LoewnerRestart.normalizedTest a z τ (subdiskMass a M.mass (subdiskRadius M.radiusIndex) l))

lemma testEndpoint_pos (τ : ℝ) (hτ : 0<τ) (l : ℕ) : 0<τ*Real.exp (-2*a*l) := by positivity

include ha in
lemma testEndpoint_le (τ : ℝ) (hτ : 0 ≤ τ) (l : ℕ) : τ*Real.exp (-2*a*l) ≤ τ :=
  mul_le_of_le_one_right hτ (Real.exp_le_one_iff.mpr (by
    have hl : (0:ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith))

lemma stoppedTest_measurable (z : ℂ) (hz : 0<z.im) (τ : ℝ) (hτ : 0<τ)
    (hτz : τ ≤ z.im) (l : ℕ) :
    Measurable[(radialTime_stopping a (by linarith) z hz (τ*Real.exp (-2*a*l))
      ((testEndpoint_pos (a := a)) τ hτ l) (((testEndpoint_le (ha := ha)) τ hτ.le l).trans hτz)).measurableSpace]
      (M.stoppedTest z τ l) :=
  finiteStoppedTest_raw_measurable _ _
    (normalizedTest_measurable a ha z hz τ hτ hτz _ (M.subdisk_measurable l))

lemma stoppedTest_eq (z : ℂ) (hz : 0<z.im) (τ : ℝ) (hτ : 0<τ)
    (hτz : τ ≤ z.im) (l : ℕ) (b : GDriver)
    (hb : radialTime a b.1 z (τ*Real.exp (-2*a*l))≠∞) :
    M.stoppedTest z τ l b=LoewnerRestart.normalizedTest a z τ
      (subdiskMass a M.mass (subdiskRadius M.radiusIndex) l) b :=
  finiteStoppedTest_normalizedTest_eq a ha z hz τ hτ hτz l _
    (fun θ=>M.subdisk_raw_measurable θ l) b hb

lemma subdisk_ge_real_law (l : ℕ) (H : ℝ) (_hH : 0 ≤ H) :
    (finiteAngleLaw W a l) {p | ENNReal.ofReal H ≤ subdiskMass a M.mass (subdiskRadius M.radiusIndex) l p}=
      M.law {x | H ≤ sequenceLevelReal l x} := by
  rw [M.subdisk_ge_law]
  apply measure_congr
  filter_upwards [M.increasing_finite] with x hx
  exact propext (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top hx.2.ne (le_iSup x l)))

 

theorem stopped_success_lower [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (z : ℂ) (hz : 0<z.im) (σ τ : ℝ) (hτ : 0<τ) (hτσ : τ ≤ σ) (hσz : σ ≤ z.im)
    (s : ℝ) (hs : Jacobi.mixingTime (4*a) ≤ s) (hgap : τ=σ*Real.exp (-2*a*s))
    (l : ℕ) (H : ℝ) (hH : 0 ≤ H) (A : Set GDriver)
    (hA : MeasurableSet[(radialTime_stopping a (by linarith) z hz σ
      (hτ.trans_le hτσ) hσz).measurableSpace] A) :
    (1/2:ℝ≥0∞)*M.law {x | H ≤ sequenceLevelReal l x}*
        radialLaw W a z (τ*Real.exp (-2*a*l)) A  ≤ 
      radialLaw W a z (τ*Real.exp (-2*a*l))
        (A∩{b | ENNReal.ofReal H ≤ M.stoppedTest z τ l b}) := by
  let E : Set (Angle×GDriver) :=
    {p | ENNReal.ofReal H ≤ subdiskMass a M.mass (subdiskRadius M.radiusIndex) l p}
  have hE : MeasurableSet E := measurableSet_le measurable_const (M.subdisk_measurable l)
  have hh := (normalizedTest_conditional_bounds W hW a ha z hz σ τ hτ hτσ hσz s hs hgap
    l A hA (E.indicator (fun _=>(1:ℝ≥0∞))) (measurable_const.indicator hE)).1
  rw [lintegral_indicator hE,lintegral_one,Measure.restrict_apply_univ,
    M.subdisk_ge_real_law l H hH] at hh
  refine hh.trans_eq ?_
  have hm := M.stoppedTest_measurable z hz τ hτ (hτσ.trans hσz) l
  have hT := radialTime_stopping a (by linarith) z hz (τ*Real.exp (-2*a*l))
    ((testEndpoint_pos (a := a)) τ hτ l) (((testEndpoint_le (ha := ha)) τ hτ.le l).trans (hτσ.trans hσz))
  have hS : MeasurableSet {b | ENNReal.ofReal H ≤ M.stoppedTest z τ l b} :=
    hT.measurableSpace_le _ (measurableSet_le measurable_const hm)
  have he : (∫⁻b in A,LoewnerRestart.normalizedTest a z τ (E.indicator (fun _=>(1:ℝ≥0∞))) b
      ∂radialLaw W a z (τ*Real.exp (-2*a*l)))=
      ∫⁻b in A,{b | ENNReal.ofReal H ≤ M.stoppedTest z τ l b}.indicator
        (fun _=>(1:ℝ≥0∞)) b∂radialLaw W a z (τ*Real.exp (-2*a*l)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (radial_hit_ae W a ha z hz (τ*Real.exp (-2*a*l))
      ((testEndpoint_pos (a := a)) τ hτ l) (((testEndpoint_le (ha := ha)) τ hτ.le l).trans (hτσ.trans hσz)))] with b hb
    simp only [Set.indicator,Set.mem_ofPred_eq,M.stoppedTest_eq z hz τ hτ (hτσ.trans hσz) l b hb]
    simp [LoewnerRestart.normalizedTest,E,Set.indicator]; rfl
  rw [he,lintegral_indicator hS,lintegral_one,Measure.restrict_apply_univ,Measure.restrict_apply hS,inter_comm]

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end

end OAI
