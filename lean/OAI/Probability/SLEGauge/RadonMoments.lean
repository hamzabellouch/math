import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.LocalFiniteness

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
open Filter
open Filter Set
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MeasureTheory
open scoped Classical
open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology
open scoped ENNReal
open Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology
open MeasureTheory Filter Topology Set CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped NNReal ENNReal
theorem actual_radon_all_moments (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ)
      (μ : ExactSLEGenerator.Driver → ℕ → Measure UpperPlane),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k j, j∈s k → 0≤coeff k j) ∧
      (∀ k, ∑ j∈s k, coeff k j=1) ∧
      (∀ b i, IsFiniteMeasureOnCompacts (μ b i) ∧ (μ b i).Regular) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)),
        AEStronglyMeasurable (fun b => ∫ z, f z ∂μ b i) W) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ b i) (m : ℝ≥0∞) W) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i ≤ t j → μ b i ≤ μ b j) ∧
        (∀ i (f : C_c(UpperPlane, ℝ)),
          Tendsto (fun k => ∑ j∈s k, coeff k j *
            ∫ z, f z ∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫ z, f z ∂μ b i)))
 := by
  obtain ⟨s,c,μ,hs,hc,hsum,hμ,hmeas,h⟩ := actual_ordered_radon_extraction a ha W hW t
  refine ⟨s,c,μ,hs,hc,hsum,hμ,hmeas,?_,h⟩
  intro i f m
  apply actual_radon_limit_memLp a ha W hW (t i) s c hc hsum (fun b => μ b i) f _ m
  filter_upwards [h] with b hb
  exact hb.2 i f

end ExactSLEGreen

namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped NNReal ENNReal

lemma unifIntegrable_of_L2_bound {Ω : Type*} [MeasurableSpace Ω]
    (W : Measure Ω) (F : ℕ → Ω → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) W)
    (C : ℝ≥0∞) (hC : C<∞) (hbound : ∀ n, eLpNorm (F n) 2 W≤C) :
    UnifIntegrable F 1 W := by
  apply unifIntegrable_iff.mpr
  intro ε hε
  have ht : Tendsto (fun δ : ℝ => C * (ENNReal.ofReal δ)^((1:ℝ)/2)) (𝓝 0) (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (1:ℝ)/2)).continuousAt.tendsto.comp
      (ENNReal.continuous_ofReal.continuousAt.tendsto (x := (0:ℝ)))
    have hzero : (ENNReal.ofReal (0:ℝ))^((1:ℝ)/2)=(0:ℝ≥0∞) := by simp
    rw [hzero] at h
    simpa using ENNReal.Tendsto.const_mul h (Or.inr hC.ne)
  obtain ⟨r,hr,hrb⟩ := Metric.eventually_nhds_iff.mp
    ((tendsto_order.mp ht).2 ε hε)
  have hδ : 0<r/2 := by positivity
  have hsml : C*(ENNReal.ofReal (r/2))^((1:ℝ)/2)<ε :=
    hrb (y := r/2) (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; linarith)
  refine ⟨ENNReal.ofReal (r/2),ENNReal.ofReal_pos.mpr hδ,?_⟩
  intro n s hWs
  calc
    _ ≤ eLpNorm (F n) 2 (W.restrict s) * (W s)^((1:ℝ)/2) := by
      convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := W.restrict s) (by norm_num : (1:ℝ≥0∞)≤2) (hF n).restrict using 1
      norm_num
    _ ≤ C*(ENNReal.ofReal (r/2))^((1:ℝ)/2) := by
      gcongr
      exact (eLpNorm_mono_measure (F n) Measure.restrict_le_self).trans (hbound n)
    _ ≤ ε := hsml.le

lemma actual_radon_limit_L1 (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℝ≥0∞) (q : ℕ → ℝ) (hq : ∀ j,0<q j) (hq1 : ∀ j,q j≤1)
    (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ)
    (hc : ∀ k j,j∈s k→0≤coeff k j) (hsum : ∀ k,∑j∈s k,coeff k j=1)
    (μ : ExactSLEGenerator.Driver → Measure UpperPlane) (f : C_c(UpperPlane,ℝ))
    (hlim : ∀ᵐ b∂W, Tendsto (fun k => ∑j∈s k,coeff k j*
      ∫z,f z∂actualUpperMass a (q j) t b) atTop (𝓝 (∫z,f z∂μ b))) :
    Tendsto (fun k => eLpNorm (fun b => (∑j∈s k,coeff k j*
      ∫z,f z∂actualUpperMass a (q j) t b)-(∫z,f z∂μ b)) 1 W) atTop (𝓝 0) := by
  let F := fun k b => ∑j∈s k,coeff k j*∫z,f z∂actualUpperMass a (q j) t b
  have hF (k : ℕ) : AEStronglyMeasurable (F k) W := by
    have H := Finset.aestronglyMeasurable_sum (μ := W) (s k) (fun j hj =>
      (actualUpperMass_eval_measurable a ha (q j) (hq j) (hq1 j) t f).aestronglyMeasurable.const_mul (coeff k j))
    convert H using 1
    funext b
    simp only [F,Finset.sum_apply]
  obtain ⟨C,hC,hCb⟩ := actualUpperMass_Lp_bound a ha W hW 2 (by norm_num) f
  have hbound (k : ℕ) : eLpNorm (F k) 2 W≤C :=
    convex_eLpNorm_bound W _ C (by norm_num) (s k) (coeff k) (hc k) (hsum k)
      (fun j b => ∫z,f z∂actualUpperMass a (q j) t b)
      (fun j hj => (hCb (q j) (hq j) (hq1 j) t).1.aestronglyMeasurable)
      (fun j hj => (hCb (q j) (hq j) (hq1 j) t).2)
  have hg2 : MemLp (fun b => ∫z,f z∂μ b) 2 W :=
    (Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound) hF
      (aestronglyMeasurable_of_tendsto_ae atTop hF hlim) hlim).trans_lt hC
  have hg := hg2.mono_exponent (by norm_num : (1:ℝ≥0∞)≤2)
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp) hF (by simpa using hg)
    (unifIntegrable_of_L2_bound W F hF C hC hbound) hlim

 

theorem actual_radon_L1_convergence (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ)
      (μ : ExactSLEGenerator.Driver → ℕ → Measure UpperPlane),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k j, j∈s k → 0≤coeff k j) ∧
      (∀ k, ∑ j∈s k, coeff k j=1) ∧
      (∀ b i, IsFiniteMeasureOnCompacts (μ b i) ∧ (μ b i).Regular) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ b i) (m : ℝ≥0∞) W) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, coeff k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            - ∫z,f z∂μ b i) 1 W) atTop (𝓝 0)) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i ≤ t j → μ b i ≤ μ b j) ∧
        (∀ i (f : C_c(UpperPlane, ℝ)),
          Tendsto (fun k => ∑ j∈s k, coeff k j *
            ∫ z, f z ∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫ z, f z ∂μ b i)))
 := by
  obtain ⟨s,c,μ,hs,hc,hsum,hμ,hmeas,hmom,h⟩ := actual_radon_all_moments a ha W hW t
  refine ⟨s,c,μ,hs,hc,hsum,hμ,hmom,?_,h⟩
  intro i f
  have hq1 (j : ℕ) : Real.exp (-2*a*(j+1))≤1 := by
    apply Real.exp_le_one_iff.mpr
    have ha0 : 0<a := by linarith
    have hj0 : (0:ℝ)≤j := Nat.cast_nonneg _
    nlinarith
  apply actual_radon_limit_L1 a ha W hW (t i)
    (fun j => Real.exp (-2*a*(j+1)))
    (fun j => Real.exp_pos _) hq1 s c hc hsum (fun b => μ b i) f
  filter_upwards [h] with b hb
  exact hb.2 i f

end ExactSLEGreen

namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped NNReal ENNReal

lemma actualMassEval_joint_integrable (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) (t : ℝ≥0∞)
    (K : Set ℂ) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (c : ℝ) (hc : 0<c) (hcK : ∀ z,z∈K→c≤2*z.im)
    (f : ℂ → ℝ) (hf : Measurable f) (hfB : ∃ B : ℝ,0≤B ∧ ∀ z∈K,‖f z‖≤B) :
    Integrable (fun p : ExactSLEGenerator.Driver × ℂ =>
      f p.2 * (timeMassDensity a q t p.1 p.2).toReal) (W.prod (volume.restrict K)) := by
  obtain ⟨B,hB,hBf⟩ := hfB
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hKb.measure_lt_top⟩
  have hm : Measurable (fun p : ExactSLEGenerator.Driver × ℂ =>
      f p.2 * (timeMassDensity a q t p.1 p.2).toReal) :=
    (hf.comp measurable_snd).mul (timeMassDensity_measurable a ha q hq hq1 t).ennreal_toReal
  apply Integrable.of_bound hm.aestronglyMeasurable (B*((c*q)^(-alpha a)))
  have hmem : ∀ᵐ p ∂W.prod (volume.restrict K), p.2∈K :=
    (Measure.ae_prod_iff_ae_ae (hK.preimage measurable_snd)).mpr
      (Eventually.of_forall fun _ => ae_restrict_mem hK)
  filter_upwards [hmem] with p hp
  have hb := timeMassDensity_local_bound a ha q hq hq1 t p.1 c hc p.2 (hcK _ hp)
  have hD : 0≤(c*q)^(-alpha a) := Real.rpow_nonneg (by positivity) _
  have hd : (timeMassDensity a q t p.1 p.2).toReal≤(c*q)^(-alpha a) := by
    exact ENNReal.toReal_le_of_le_ofReal hD hb
  rw [norm_mul,Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul (hBf _ hp) hd ENNReal.toReal_nonneg hB

lemma terminal_density_mean (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) (z : ℂ) (hz : 0<z.im) :
    (∫b, (timeMassDensity a q ∞ b z).toReal ∂W) =
      Real.exp (-alpha a*Real.log 2)*physicalGreen a (z,0) := by
  have hnon (b : ExactSLEGenerator.Driver) :=
    (fullRadialDensity_bound a ha z hz (2*z.im*q) (by positivity) (by nlinarith) b).1
  simp only [timeMassDensity,le_top,ite_true,massDensity,hz,ENNReal.toReal_ofReal (hnon _)]
  have he : 2*z.im*q/2=z.im*q := by ring
  simp only [fullRadialDensity,he]
  rw [integral_const_mul]
  congr 1
  exact (radialWeight_mean W hW a ha z hz (z.im*q) (by positivity) (by nlinarith)).2

lemma actualMassEval_terminal_mean (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (K : Set ℂ) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (c : ℝ) (hc : 0<c) (hcK : ∀ z,z∈K→c≤2*z.im)
    (f : ℂ → ℝ) (hf : Measurable f) (hfB : ∃ B : ℝ,0≤B ∧ ∀ z∈K,‖f z‖≤B) :
    (∫b,actualMassEval a q ∞ K f b∂W) =
      ∫z in K, f z*(Real.exp (-alpha a*Real.log 2)*physicalGreen a (z,0)) := by
  unfold actualMassEval
  rw [integral_integral_swap (actualMassEval_joint_integrable a ha W q hq hq1 ∞ K hK hKb c hc hcK f hf hfB)]
  apply setIntegral_congr_fun hK
  intro z hz
  dsimp only
  rw [integral_const_mul,terminal_density_mean a ha W hW q hq hq1 z (by have := hcK z hz; linarith)]

lemma actualUpperMass_terminal_mean (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) (f : C_c(UpperPlane,ℝ)) :
    (∫b, (∫z,f z∂actualUpperMass a q ∞ b) ∂W) = ∫z : UpperPlane,
      f z*(Real.exp (-alpha a*Real.log 2)*physicalGreen a (z.1,0)) ∂upperArea := by
  let K := Subtype.val '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_subtype_val
  obtain ⟨c,hc,hcK⟩ := upper_compact_lower (tsupport f) f.hasCompactSupport
  simp_rw [actualUpperMass_eval a ha q hq hq1]
  rw [actualMassEval_terminal_mean a ha W hW q hq hq1 K hK.measurableSet hK.isBounded c hc
    (by rintro z ⟨w,hw,rfl⟩; exact hcK w hw) (upperExtension f)
    (upperExtension_measurable f) (upperExtension_bounded f)]
  simp_rw [← upperExtension_apply f]
  trans ∫z in {z : ℂ | 0<z.im},
    upperExtension f z*(Real.exp (-alpha a*Real.log 2)*physicalGreen a (z,0))
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
    · rw [upperExtension_zero f z (by rintro ⟨w,hw,rfl⟩; exact hz w.2), zero_mul]
    · rw [upperExtension_zero f z hz, zero_mul]
  · exact (integral_subtype_comap (μ := (volume : Measure ℂ)) upperPlane_open.measurableSet
      (fun z : ℂ => upperExtension f z*(Real.exp (-alpha a*Real.log 2)*physicalGreen a (z,0)))).symm

lemma actual_radon_limit_mean (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ)
    (hsum : ∀ k,∑j∈s k,coeff k j=1)
    (μ : ExactSLEGenerator.Driver → Measure UpperPlane) (f : C_c(UpperPlane,ℝ))
    (hg : MemLp (fun b => ∫z,f z∂μ b) 1 W)
    (hlim : Tendsto (fun k => eLpNorm (fun b => (∑j∈s k,coeff k j*
      ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) ∞ b)-(∫z,f z∂μ b)) 1 W) atTop (𝓝 0)) :
    (∫b, (∫z,f z∂μ b) ∂W) = ∫z : UpperPlane,
      f z*(Real.exp (-alpha a*Real.log 2)*physicalGreen a (z.1,0)) ∂upperArea := by
  let q (j : ℕ) := Real.exp (-2*a*(j+1))
  have hq (j : ℕ) : 0<q j := Real.exp_pos _
  have hq1 (j : ℕ) : q j≤1 := by
    apply Real.exp_le_one_iff.mpr
    have ha0 : 0<a := by linarith
    have hj0 : (0:ℝ)≤j := Nat.cast_nonneg _
    nlinarith
  let F := fun k b => ∑j∈s k,coeff k j*∫z,f z∂actualUpperMass a (q j) ∞ b
  obtain ⟨C,hC,hCb⟩ := actualUpperMass_Lp_bound a ha W hW 1 (by norm_num) f
  have hFi (k : ℕ) : Integrable (F k) W :=
    integrable_finsetSum (s k) (fun j hj =>
      ((hCb (q j) (hq j) (hq1 j) ∞).1.integrable (by norm_num)).const_mul (coeff k j))
  change Tendsto (fun k => eLpNorm (fun b => F k b - ∫z,f z∂μ b) 1 W) atTop (𝓝 0) at hlim
  have ht := tendsto_integral_of_L1 (fun b => ∫z,f z∂μ b) hg.aestronglyMeasurable
    (Eventually.of_forall hFi) (by
      exact hlim.congr fun index => eLpNorm_one_eq_lintegral_enorm
        ((hFi index).aestronglyMeasurable.sub hg.aestronglyMeasurable))
  have he (k : ℕ) : (∫b,F k b∂W) = ∫z : UpperPlane,
      f z*(Real.exp (-alpha a*Real.log 2)*physicalGreen a (z.1,0)) ∂upperArea := by
    dsimp only [F]
    rw [integral_finsetSum _ (fun j hj =>
      ((hCb (q j) (hq j) (hq1 j) ∞).1.integrable (by norm_num)).const_mul (coeff k j))]
    simp_rw [integral_const_mul]
    simp_rw [actualUpperMass_terminal_mean a ha W hW _ (hq _) (hq1 _) f]
    rw [← Finset.sum_mul,hsum k,one_mul]
  exact tendsto_nhds_unique ht (by simpa only [he] using tendsto_const_nhds)

 

theorem actual_radon_terminal_mean (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ)
      (μ : ExactSLEGenerator.Driver → ℕ → Measure UpperPlane),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k j, j∈s k → 0≤coeff k j) ∧
      (∀ k, ∑ j∈s k, coeff k j=1) ∧
      (∀ b i, IsFiniteMeasureOnCompacts (μ b i) ∧ (μ b i).Regular) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ b i) (m : ℝ≥0∞) W) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, coeff k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            - ∫z,f z∂μ b i) 1 W) atTop (𝓝 0)) ∧
      (∀ i, t i=∞ → ∀ f : C_c(UpperPlane,ℝ),
        (∫b, (∫z,f z∂μ b i) ∂W) = ∫z : UpperPlane,
          f z * (Real.exp (-alpha a*Real.log 2)*physicalGreen a (z.1,0)) ∂upperArea) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i ≤ t j → μ b i ≤ μ b j) ∧
        (∀ i (f : C_c(UpperPlane, ℝ)),
          Tendsto (fun k => ∑ j∈s k, coeff k j *
            ∫ z, f z ∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫ z, f z ∂μ b i)))
 := by
  obtain ⟨s,c,μ,hs,hc,hsum,hμ,hmom,hL1,h⟩ := actual_radon_L1_convergence a ha W hW t
  refine ⟨s,c,μ,hs,hc,hsum,hμ,hmom,hL1,?_,h⟩
  intro i hi f
  apply actual_radon_limit_mean a ha W hW s c hsum (fun b => μ b i) f
    (by simpa using hmom i f 1)
  simpa only [hi] using hL1 i f

end ExactSLEGreen

namespace ExactSLEGenerator
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable def pastDriver (t : ℝ≥0) (b : Driver) : Driver :=
  ⟨⟨fun s => b.1 (min s t), b.1.continuous.comp (continuous_id.min continuous_const)⟩, by simpa using b.2⟩
lemma pastDriver_eq (t : ℝ≥0) (b : Driver) (s : ℝ≥0) (hs : s≤t) :
    (pastDriver t b).1 s = b.1 s := by simp [pastDriver,min_eq_left hs]
lemma pastDriver_raw_measurable (t : ℝ≥0) : Measurable[rawFiltration t] (pastDriver t) := by
  have : PolishSpace Driver := (isClosed_eq (continuous_eval_const 0) continuous_const).polishSpace
  obtain ⟨u,hu⟩ := TopologicalSpace.exists_dense_seq (α:=ℝ≥0)
  let e : Driver → (ℕ → ℝ) := fun b n => b.1 (u n)
  have hec : Continuous e := continuous_pi fun n => (continuous_eval_const (u n)).comp continuous_subtype_val
  have hei : Function.Injective e := by
    intro b c h
    apply Subtype.ext
    apply DFunLike.coe_injective
    exact hu.equalizer b.1.continuous c.1.continuous h
  have hem := hec.measurableEmbedding hei
  apply hem.measurable_comp_iff.mp
  let : MeasurableSpace Driver := rawFiltration t
  apply measurable_pi_iff.mpr
  intro n
  exact ((Filtration.stronglyAdapted_natural driver_eval_measurable) (min (u n) t)).measurable.mono
    (rawFiltration.mono (min_le_right _ _)) le_rfl
end ExactSLEGenerator
namespace ExactSLEMain
open MeasureTheory ExactSLEGenerator
open scoped NNReal ENNReal
lemma odeUntil_driver_congr {a : ℝ} {b c : ℝ≥0 → ℝ} {z : ℂ} {t : ℝ≥0}
    (h : ∀ s≤t, b s=c s) {f : ℝ → ℂ} (hf : odeUntil a b z t f) : odeUntil a c z t f := by
  refine ⟨hf.1,fun u hu => ?_⟩
  have he := h u.toNNReal ((Real.toNNReal_le_iff_le_coe).mpr hu.2)
  simpa only [he] using hf.2 u hu
lemma alive_driver_congr {a : ℝ} {b c : ℝ≥0 → ℝ} {z : ℂ} {t : ℝ≥0}
    (h : ∀ s≤t, b s=c s) : alive a b t z ↔ alive a c t z := by
  exact ⟨fun ⟨f,hf⟩ => ⟨f,odeUntil_driver_congr h hf⟩,
    fun ⟨f,hf⟩ => ⟨f,odeUntil_driver_congr (fun s hs => (h s hs).symm) hf⟩⟩
lemma loewnerMap_driver_congr {a : ℝ} {b c : ℝ≥0 → ℝ} {t : ℝ≥0}
    (h : ∀ s≤t, b s=c s) : loewnerMap a b t = loewnerMap a c t := by
  funext z
  by_cases hb : alive a b t z
  · obtain ⟨f,hf⟩ := hb
    exact (loewnerMap_eq hf).trans (loewnerMap_eq (odeUntil_driver_congr h hf)).symm
  · have hc := mt (alive_driver_congr h).mpr hb
    simp [loewnerMap,hb,hc]
end ExactSLEMain
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal
lemma actualState_driver_congr {a : ℝ} {b c : ℝ≥0 → ℝ} {t : ℝ≥0} (h : ∀ s≤t,b s=c s) (z : ℂ) :
    actualState a b t z = actualState a c t z := by
  simp only [actualState,loewnerMap_driver_congr h,h t le_rfl]
lemma radialTime_driver_congr_before (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im) (b c : ExactSLEGenerator.Driver) (t : ℝ≥0)
    (h : ∀ s≤t,b.1 s=c.1 s) (hb : radialTime a b.1 z ρ≤t) :
    radialTime a b.1 z ρ = radialTime a c.1 z ρ := by
  have hbfin : radialTime a b.1 z ρ≠∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hb
  have hbr : (radialTime a b.1 z ρ).toNNReal≤t := by
    exact ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_toNNReal hbfin] using hb)
  obtain ⟨hba,hbh⟩ := radialTime_attained a ha z hz ρ hρ hr b hbfin
  have he := actualState_driver_congr (a:=a) (fun s hs => h s (hs.trans hbr)) z
  have hc : radialTime a c.1 z ρ≤radialTime a b.1 z ρ := by
    have hh := radialTime_le_of_hit a z ρ c (radialTime a b.1 z ρ).toNNReal
      ((alive_driver_congr (fun s hs => h s (hs.trans hbr))).mp hba) (by rw [← he]; exact hbh)
    simpa only [ENNReal.coe_toNNReal hbfin] using hh
  have hcfin : radialTime a c.1 z ρ≠∞ := ne_top_of_le_ne_top hbfin hc
  have hcr : (radialTime a c.1 z ρ).toNNReal≤t := by
    exact ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_toNNReal hcfin] using hc.trans hb)
  obtain ⟨hca,hch⟩ := radialTime_attained a ha z hz ρ hρ hr c hcfin
  have he' := actualState_driver_congr (a:=a) (fun s hs => (h s (hs.trans hcr)).symm) z
  have hh := radialTime_le_of_hit a z ρ b (radialTime a c.1 z ρ).toNNReal
    ((alive_driver_congr (fun s hs => (h s (hs.trans hcr)).symm)).mp hca) (by rw [← he']; exact hch)
  exact le_antisymm (by simpa only [ENNReal.coe_toNNReal hcfin] using hh) hc
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal
lemma timeMassDensity_driver_congr (a : ℝ) (ha : 0<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (b c : ExactSLEGenerator.Driver) (t : ℝ≥0) (h : ∀ s≤t,b.1 s=c.1 s) (z : ℂ) :
    timeMassDensity a q t b z = timeMassDensity a q t c z := by
  by_cases hz : 0<z.im
  · have hρ : 0<z.im*q := mul_pos hz hq
    have hr : z.im*q≤z.im := by nlinarith
    have hiff : radialTime a b.1 z (z.im*q)≤t ↔ radialTime a c.1 z (z.im*q)≤t := by
      constructor
      · intro hb
        rwa [← radialTime_driver_congr_before a ha z hz _ hρ hr b c t h hb]
      · intro hc
        rwa [← radialTime_driver_congr_before a ha z hz _ hρ hr c b t (fun s hs => (h s hs).symm) hc]
    by_cases hb : radialTime a b.1 z (z.im*q)≤t
    · have he := radialTime_driver_congr_before a ha z hz _ hρ hr b c t h hb
      have hfin : radialTime a b.1 z (z.im*q)≠∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hb
      have ht : (radialTime a b.1 z (z.im*q)).toNNReal≤t := by
        exact ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_toNNReal hfin] using hb)
      have hs := actualState_driver_congr (a:=a) (fun s hs => h s (hs.trans ht)) z
      have hw : radialWeight a b.1 z (z.im*q)=radialWeight a c.1 z (z.im*q) := by
        unfold radialWeight
        rw [ite_eq_right hfin,ite_eq_right (ne_of_eq_of_ne he.symm hfin),← he,hs]
      have hn : 2*z.im*q/2=z.im*q := by ring
      simp only [timeMassDensity,ite_eq_left hb,ite_eq_left (hiff.mp hb),massDensity,ite_eq_left hz,fullRadialDensity,hn,hw]
    · simp only [timeMassDensity,ite_eq_right hb,ite_eq_right (mt hiff.mpr hb)]
  · simp only [timeMassDensity,massDensity,ite_eq_right hz,ite_self]
lemma timeMassDensity_past_eq (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q)
    (hq1 : q≤1) (t : ℝ≥0) :
    (fun p : ExactSLEGenerator.Driver × ℂ => timeMassDensity a q t p.1 p.2) =
    (fun p : ExactSLEGenerator.Driver × ℂ => timeMassDensity a q t (pastDriver t p.1) p.2) := by
  funext p
  exact timeMassDensity_driver_congr a (by linarith) q hq hq1 p.1 (pastDriver t p.1) t
    (fun s hs => (pastDriver_eq t p.1 s hs).symm) p.2
lemma rawPastPair_measurable (t : ℝ≥0) :
    @Measurable (ExactSLEGenerator.Driver × ℂ) (ExactSLEGenerator.Driver × ℂ)
      ((rawFiltration t).prod (borel ℂ)) inferInstance (fun p => (pastDriver t p.1,p.2)) := by
  exact ((pastDriver_raw_measurable t).comp
    (@measurable_fst _ _ (rawFiltration t) (borel ℂ))).prodMk
    (@measurable_snd _ _ (rawFiltration t) (borel ℂ))
 
theorem timeMassDensity_raw_joint (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q)
    (hq1 : q≤1) (t : ℝ≥0) :
    letI : MeasurableSpace ExactSLEGenerator.Driver := rawFiltration t
    Measurable (fun p : ExactSLEGenerator.Driver × ℂ => timeMassDensity a q t p.1 p.2) := by
  change @Measurable (ExactSLEGenerator.Driver × ℂ) ℝ≥0∞
    ((rawFiltration t).prod (borel ℂ)) inferInstance _
  rw [timeMassDensity_past_eq a ha q hq hq1 t]
  exact @Measurable.comp (ExactSLEGenerator.Driver × ℂ) (ExactSLEGenerator.Driver × ℂ) ℝ≥0∞
    ((rawFiltration t).prod (borel ℂ)) inferInstance inferInstance
    (fun p => timeMassDensity a q (t : ℝ≥0∞) p.1 p.2)
    (fun p => (pastDriver t p.1,p.2))
    (timeMassDensity_measurable a ha q hq hq1 (t : ℝ≥0∞)) (rawPastPair_measurable t)
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal Topology
end ExactSLEGreen
end
end

end OAI
