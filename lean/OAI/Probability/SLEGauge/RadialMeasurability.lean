import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.MassMoments

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
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
theorem joint_radialTime_measurable (a : ℝ) (ha : 1/4 < a) (q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    Measurable (fun p : ExactSLEGenerator.Driver × {z : ℂ // 0 < z.im} =>
      radialTime a p.1.1 p.2.1 (p.2.1.im*q)) := by
  have ha0 : 0<a := by linarith
  let Ω := ExactSLEGenerator.Driver × {z : ℂ // 0 < z.im}
  let z : Ω → ℂ := fun p => p.2.1
  let b : Ω → ExactSLEGenerator.Driver := Prod.fst
  have hz (ω : Ω) : 0<(z ω).im := ω.2.2
  have hzM : Measurable z := measurable_subtype_coe.comp measurable_snd
  have hbM : Measurable b := measurable_fst
  let ρ : Ω → ℝ := fun ω => (z ω).im*q
  have hρ (ω : Ω) : 0<ρ ω := mul_pos (hz ω) hq
  have hr (ω : Ω) : ρ ω≤(z ω).im := mul_le_of_le_one_right (hz ω).le hq1
  let δ : ℕ → Ω → ℝ := fun n ω => angleThreshold (z ω) n
  let L (n : ℕ) (ω : Ω) := explicitRadialLocalization a ha0 (z ω) (hz ω) (ρ ω) (δ n ω)
    (hρ ω) (hr ω) (angleThreshold_pos (z ω) (hz ω) n) (angleThreshold_initial (z ω) (hz ω) n)
  have hρM : Measurable ρ := hzM.im.mul_const q
  have hδM (n : ℕ) : Measurable (δ n) := by
    dsimp [δ,angleThreshold]
    exact (hzM.im.div hzM.norm).div_const _
  have hεM (n : ℕ) : Measurable (fun ω => (L n ω).ε) := by
    change Measurable (fun ω => heightFloor (z ω).im (ρ ω) (δ n ω)/2)
    unfold heightFloor
    fun_prop
  have hNM (n : ℕ) : Measurable (fun ω => (L n ω).N) := by
    change Measurable (fun ω => (⟨(z ω).im/δ n ω+logCeiling (z ω).im (ρ ω) (δ n ω)+1, _⟩ : ℝ≥0))
    apply Measurable.subtype_mk
    unfold logCeiling heightFloor
    fun_prop
  have hBM (n : ℕ) : Measurable (fun ω => (L n ω).B) := by
    change Measurable (fun ω => (⟨(z ω).im^2/(2*a*(δ n ω)^2)+1, _⟩ : ℝ≥0))
    apply Measurable.subtype_mk
    fun_prop
  let T (n : ℕ) (ω : Ω) := regionStop a (L n ω).ε (L n ω).hε (z ω)
    (L n ω).N (ρ ω) (δ n ω) (L n ω).B (b ω)
  have hTM (n : ℕ) : Measurable (T n) :=
    regionStop_parameter_measurable a (fun ω => (L n ω).ε) (fun ω => (L n ω).hε) z b _ ρ (δ n) _ (hεM n) hzM hbM
      (measurable_subtype_coe.comp (hNM n)) hρM (hδM n) (hBM n)
  let V (n : ℕ) (ω : Ω) := localState a (L n ω).ε (L n ω).hε (z ω) (T n ω) (b ω)
  have hVM (n : ℕ) : Measurable (V n) :=
    ((localState_parameter_joint_measurable a (fun ω => (L n ω).ε) (fun ω => (L n ω).hε)
      z b (hεM n) hzM hbM).comp ((hTM n).prodMk measurable_id))
  apply measurable_of_Iic
  intro t
  by_cases ht : t=∞
  · subst t
    simp
  have he : (fun ω : Ω => radialTime a (b ω).1 (z ω) (ρ ω)) ⁻¹' Iic t =
      ⋃ n : ℕ, {ω | T n ω ≤ t.toNNReal} ∩ {ω | physicalRadius (V n ω) = ρ ω} := by
    ext ω
    simp only [mem_preimage,mem_Iic,mem_iUnion,mem_inter_iff,mem_ofPred_eq]
    constructor
    · intro hrt
      have hfin : radialTime a (b ω).1 (z ω) (ρ ω) ≠ ∞ := ne_top_of_le_ne_top ht hrt
      let r := (radialTime a (b ω).1 (z ω) (ρ ω)).toNNReal
      have hhit := radialTime_attained a ha0 (z ω) (hz ω) (ρ ω) (hρ ω) (hr ω) (b ω) hfin
      obtain ⟨η,hη,hηs⟩ := actual_sine_lower a (b ω).1 (b ω).1.continuous (z ω) r hhit.1
      obtain ⟨n,hn⟩ := ((angleThreshold_tendsto (z ω)).eventually (gt_mem_nhds hη)).exists
      have hTr : T n ω≤r := regionStop_le_hit a (L n ω).ε (L n ω).hε (z ω)
        (L n ω).N (ρ ω) (δ n ω) (L n ω).B (L n ω).initial (b ω) r hhit.2
      have hrt' : r≤t.toNNReal := ENNReal.toNNReal_mono ht hrt
      refine ⟨n,hTr.trans hrt',?_⟩
      rcases regionStop_true_exit a (L n ω).ε ha0 (L n ω).hε (z ω) (L n ω).N
        (ρ ω) (δ n ω) (hρ ω) (angleThreshold_pos (z ω) (hz ω) n) (L n ω).B
        (L n ω).initial (L n ω).small (L n ω).large (L n ω).time (b ω) with hR|hS
      · exact hR
      · have hact := regionStop_actualState a (L n ω).ε (L n ω).hε (z ω) (L n ω).N
          (ρ ω) (δ n ω) (L n ω).B (L n ω).initial (b ω) (T n ω) le_rfl
        have hs := regionStop_safe a (L n ω).ε (L n ω).hε (z ω) (L n ω).N
          (ρ ω) (δ n ω) (L n ω).B (L n ω).initial (b ω) (T n ω) le_rfl
        have hp : 0 < ‖(V n ω).1‖ := ((L n ω).hε.trans_le hs.1).trans_le (Complex.im_le_norm _)
        have hd : Y (V n ω)/‖(V n ω).1‖ = δ n ω := (div_eq_iff hp.ne').mpr hS
        have hη' := hηs (T n ω) hTr
        rw [hact.2,hd] at hη'
        exact False.elim (not_le.mpr hn hη')
    · rintro ⟨n,hnt,hR⟩
      have heq := regionStop_eq_radialTime a (L n ω).ε (L n ω).hε (z ω) (L n ω).N
        (ρ ω) (δ n ω) (L n ω).B (L n ω).initial (b ω) hR
      rw [heq]
      exact (ENNReal.coe_le_coe.mpr hnt).trans_eq (ENNReal.coe_toNNReal ht)
  rw [he]
  exact MeasurableSet.iUnion (fun n => (measurableSet_le (hTM n) measurable_const).inter
    (measurableSet_eq_fun (physicalRadius_continuous.measurable.comp (hVM n)) hρM))

theorem joint_radial_approximant_measurable (a : ℝ) (ha : 1/4 < a) (q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    Measurable (fun p : (ExactSLEGenerator.Driver × {z : ℂ // 0 < z.im}) × ℝ≥0∞ =>
      if radialTime a p.1.1.1 p.1.2.1 (p.1.2.1.im*q) ≤ p.2 then
        radialWeight a p.1.1.1 p.1.2.1 (p.1.2.1.im*q) else 0) := by
  exact ((joint_radialWeight_measurable a ha q hq hq1).comp measurable_fst).ite
    (measurableSet_le ((joint_radialTime_measurable a ha q hq hq1).comp measurable_fst) measurable_snd)
    measurable_const
end ExactSLEGreen
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Set Filter Topology
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped Classical NNReal ENNReal
noncomputable def timeMassDensity (a q : ℝ) (t : ℝ≥0∞)
    (b : ExactSLEGenerator.Driver) (z : ℂ) : ℝ≥0∞ :=
  if radialTime a b.1 z (z.im*q) ≤ t then massDensity a q b z else 0
noncomputable def actualMassEval (a q : ℝ) (t : ℝ≥0∞)
    (K : Set ℂ) (f : ℂ → ℝ) (b : ExactSLEGenerator.Driver) : ℝ :=
  ∫ z in K, f z * (timeMassDensity a q t b z).toReal
lemma timeMassDensity_le (a q : ℝ) (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) (z : ℂ) :
    timeMassDensity a q t b z ≤ massDensity a q b z := by
  unfold timeMassDensity
  split_ifs <;> simp

lemma timeMassDensity_measurable (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (t : ℝ≥0∞) :
    Measurable (fun p : ExactSLEGenerator.Driver × ℂ => timeMassDensity a q t p.1 p.2) := by
  let U : Set (ExactSLEGenerator.Driver × ℂ) := {p | 0<p.2.im}
  have hU : MeasurableSet U := measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_snd)
  have hm : Measurable (fun p : U => ENNReal.ofReal (Real.exp (-alpha a*Real.log 2)*
      (if radialTime a p.1.1.1 p.1.2 (p.1.2.im*q)≤t then
        radialWeight a p.1.1.1 p.1.2 (p.1.2.im*q) else 0))) := by
    have hp : Measurable (fun p : U => ((p.1.1, (⟨p.1.2,p.2⟩ : {z : ℂ // 0<z.im})),t)) := by fun_prop
    exact (measurable_const.mul ((joint_radial_approximant_measurable a ha q hq hq1).comp hp)).ennreal_ofReal
  have h := hm.dite (g:=fun _ => 0) measurable_const hU
  convert h using 1
  funext p
  have he : 2*p.2.im*q/2=p.2.im*q := by ring
  by_cases hz : 0<p.2.im <;> by_cases ht : radialTime a p.1.1 p.2 (p.2.im*q)≤t <;>
    simp [timeMassDensity,massDensity,fullRadialDensity,U,hz,ht,he]

lemma actualMassEval_measurable (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (t : ℝ≥0∞) (K : Set ℂ) (f : ℂ → ℝ) (hf : Measurable f) :
    Measurable (actualMassEval a q t K f) := by
  have hm : Measurable (fun p : ExactSLEGenerator.Driver × ℂ =>
      f p.2 * (timeMassDensity a q t p.1 p.2).toReal) :=
    (hf.comp measurable_snd).mul (timeMassDensity_measurable a ha q hq hq1 t).ennreal_toReal
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma actualMassEval_enorm_bound (a q : ℝ) (t : ℝ≥0∞) (K : Set ℂ) (f : ℂ → ℝ)
    (b : ExactSLEGenerator.Driver) :
    ‖actualMassEval a q t K f b‖ₑ ≤
      ∫⁻ z in K, ENNReal.ofReal ‖f z‖ * massDensity a q b z := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  apply lintegral_mono
  intro z
  dsimp only
  rw [enorm_mul, Real.enorm_eq_ofReal_abs, ←Real.norm_eq_abs,
    Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
  exact mul_le_mul' le_rfl (ENNReal.ofReal_toReal_le.trans (timeMassDensity_le a q t b z))

lemma actualMassEval_L2_bound (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (K : Set ℂ) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (c : ℝ) (hc : 0<c) (hcK : ∀ z, z∈K → c≤2*z.im)
    (f : ℂ → ℝ) (hf : Measurable f) (hfB : ∃ B : ℝ, 0≤B ∧ ∀ z∈K, ‖f z‖≤B) :
    ∃ C : ℝ≥0∞, C<∞ ∧ ∀ q : ℝ, 0<q → q≤1 → ∀ t : ℝ≥0∞,
      MemLp (actualMassEval a q t K f) 2 W ∧ eLpNorm (actualMassEval a q t K f) 2 W ≤ C := by
  obtain ⟨C,hC,hCb⟩ := actual_mass_moment_bound a ha 2
  obtain ⟨hAfin,hB⟩ := hCb W hW K hK hKb c hc hcK (fun z => ‖f z‖) hf.norm
    (fun _ _ => norm_nonneg _) hfB
  let A := ∫⁻ x : Fin 2 → ℂ, (∏ i, ENNReal.ofReal ‖f (x i)‖)*
    ExactSLEKernel.kernel (alpha a) c x ∂Measure.pi (fun _ => volume.restrict K)
  let D := (ENNReal.ofReal C*A)^(1/(2:ℝ))
  have hD : D<∞ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAfin).ne
  refine ⟨D,hD,?_⟩
  intro q hq hq1 t
  have hnorm : eLpNorm (actualMassEval a q t K f) 2 W≤D := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (actualMassEval_measurable a ha q hq hq1 t K f hf).aestronglyMeasurable]
    norm_num only [ENNReal.toReal_ofNat]
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    calc
      _ ≤ ∫⁻ b, (∫⁻ z in K, ENNReal.ofReal ‖f z‖*massDensity a q b z)^2 ∂W := by
        apply lintegral_mono
        intro b
        change ‖actualMassEval a q t K f b‖ₑ^(2:ℝ) ≤
          (∫⁻ z in K, ENNReal.ofReal ‖f z‖*massDensity a q b z)^(2:ℕ)
        rw [ENNReal.rpow_two]
        exact pow_le_pow_left' (actualMassEval_enorm_bound a q t K f b) 2
      _ ≤ _ := hB q hq hq1
  exact ⟨hnorm.trans_lt hD,hnorm⟩

theorem actualMassEval_integrable (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (t : ℝ≥0∞) (K : Set ℂ) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (c : ℝ) (hc : 0<c) (hcK : ∀ z, z∈K → c≤2*z.im)
    (f : ℂ → ℝ) (hf : Measurable f) (hfB : ∃ B : ℝ, 0≤B ∧ ∀ z∈K, ‖f z‖≤B)
    (b : ExactSLEGenerator.Driver) :
    Integrable (fun z => f z*(timeMassDensity a q t b z).toReal) (volume.restrict K) := by
  obtain ⟨B,hB,hBf⟩ := hfB
  let D := (c*q)^(-alpha a)
  have hD : 0≤D := Real.rpow_nonneg (mul_pos hc hq).le _
  have hd (z : ℂ) (hzK : z∈K) : (timeMassDensity a q t b z).toReal≤D := by
    have hz : 0<z.im := by have := hcK z hzK; linarith
    have hit := fullRadialDensity_bound a ha z hz (2*z.im*q) (by positivity) (by nlinarith) b
    have htar : (2*z.im*q)^(-alpha a)≤D :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hc hq) (mul_le_mul_of_nonneg_right (hcK z hzK) hq.le)
        (neg_nonpos.mpr (alpha_pos ha).le)
    have hm : massDensity a q b z≤ENNReal.ofReal D := by
      simp only [massDensity,ite_eq_left hz]
      exact ENNReal.ofReal_le_ofReal (hit.2.trans htar)
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((timeMassDensity_le a q t b z).trans hm)
    simpa only [ENNReal.toReal_ofReal hD] using hh
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hKb.measure_lt_top⟩
  have hm : Measurable (fun z => timeMassDensity a q t b z) :=
    (timeMassDensity_measurable a ha q hq hq1 t).comp (measurable_const.prodMk measurable_id)
  apply Integrable.of_bound ((hf.mul hm.ennreal_toReal).aestronglyMeasurable) (B*D)
  filter_upwards [ae_restrict_mem hK] with z hz
  change ‖f z*(timeMassDensity a q t b z).toReal‖ ≤ B*D
  rw [norm_mul,Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul (hBf z hz) (hd z hz) ENNReal.toReal_nonneg hB
theorem actual_common_mass_extraction (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (K : ℕ → Set ℂ) (hK : ∀ i, MeasurableSet (K i))
    (hKb : ∀ i, Bornology.IsBounded (K i))
    (c : ℕ → ℝ) (hc : ∀ i, 0<c i) (hcK : ∀ i z, z∈K i → c i≤2*z.im)
    (f : ℕ → ℂ → ℝ) (hf : ∀ i, Measurable (f i))
    (hfB : ∀ i, ∃ B : ℝ, 0≤B ∧ ∀ z∈K i, ‖f i z‖≤B)
    (t : ℕ → ℝ≥0∞) :
    ∃ (X : ℕ → ℕ → Lp ℝ 2 W) (s : ℕ → Finset ℕ)
      (coeff : ℕ → ℕ → ℝ) (v : ℕ → Lp ℝ 2 W),
      (∀ j i, (fun b => X j i b) =ᵐ[W]
        actualMassEval a (Real.exp (-2*a*(j+1))) (t i) (K i) (f i)) ∧
      (∀ k j, j∈s k → k≤j) ∧
      (∀ k j, j∈s k → 0≤coeff k j) ∧
      (∀ k, ∑ j∈s k, coeff k j=1) ∧
      (∀ i, Tendsto (fun k => ∑ j∈s k, coeff k j • X j i) atTop (𝓝 (v i))) ∧
      (∀ᵐ b ∂W, ∀ i, Tendsto (fun k => ∑ j∈s k, coeff k j *
        actualMassEval a (Real.exp (-2*a*(j+1))) (t i) (K i) (f i) b)
        atTop (𝓝 (v i b)))
    := by
  choose C hC hBound using fun i => actualMassEval_L2_bound a ha W hW (K i) (hK i) (hKb i)
    (c i) (hc i) (hcK i) (f i) (hf i) (hfB i)
  let q := fun j : ℕ => Real.exp (-2*a*(j+1))
  have hq (j : ℕ) : 0<q j := Real.exp_pos _
  have hq1 (j : ℕ) : q j≤1 := by
    apply Real.exp_le_one_iff.mpr
    have ha0 : 0<a := by linarith
    have hj : (0:ℝ)≤j := Nat.cast_nonneg _
    nlinarith
  let hLp := fun j i => (hBound i (q j) (hq j) (hq1 j) (t i)).1
  let X := fun j i => (hLp j i).toLp (actualMassEval a (q j) (t i) (K i) (f i))
  have hX (i : ℕ) : ∃ B : ℝ, ∀ j, ‖X j i‖≤B := by
    refine ⟨(C i).toReal,?_⟩
    intro j
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono (hC i).ne (hBound i (q j) (hq j) (hq1 j) (t i)).2
  obtain ⟨s,coeff,v,hs,hcoeff,hsum,hconv,hae⟩ := common_L2_convex_tails W X hX
  have he j i : (fun b => X j i b) =ᵐ[W] actualMassEval a (q j) (t i) (K i) (f i) :=
    (hLp j i).coeFn_toLp
  refine ⟨X,s,coeff,v,he,hs,hcoeff,hsum,hconv,?_⟩
  have heall : ∀ᵐ b ∂W, ∀ j i, X j i b=actualMassEval a (q j) (t i) (K i) (f i) b :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun i => he j i
  filter_upwards [hae,heall] with b hb heq
  intro i
  simpa only [heq] using hb i

end ExactSLEGreen

open MeasureTheory Filter Topology Set CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEMassExtraction
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem supported_dense_tests (K : Set X) (hK : IsCompact K) :
    ∃ g : ℕ → C_c(X, ℝ), (∀ i, tsupport (g i) ⊆ K) ∧
      ∀ f : C_c(X, ℝ), tsupport f ⊆ K → ∀ ε > 0,
        ∃ i, ∀ x, |f x - g i x| < ε := by
  classical
  let S := {f : C(X, ℝ) // tsupport f ⊆ K}
  have : SecondCountableTopology C(X, ℝ) := inferInstance
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  have : Nonempty S := ⟨⟨0, by simp⟩⟩
  let d := TopologicalSpace.denseSeq S
  let g : ℕ → C_c(X, ℝ) := fun i =>
    ⟨(d i).1, hK.of_isClosed_subset (isClosed_tsupport _) (d i).2⟩
  refine ⟨g, fun i => (d i).2, ?_⟩
  intro f hf ε hε
  let s : S := ⟨f.toContinuousMap, hf⟩
  have hs : s ∈ closure (range d) := TopologicalSpace.denseRange_denseSeq S s
  obtain ⟨v, hv, ht⟩ := mem_closure_iff_seq_limit.mp hs
  have ht' : Tendsto (fun n => (v n).1) atTop (𝓝 s.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp ht
  have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht') K hK
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hu ε hε).exists
  obtain ⟨i, hi⟩ := hv n
  refine ⟨i, fun x => ?_⟩
  by_cases hx : x ∈ K
  · have H := hn x hx
    rw [← hi] at H
    exact H
  · have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hf h))
    have hg0 : g i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx ((d i).2 h))
    simpa [hf0, hg0] using hε

omit [MeasurableSpace X] [BorelSpace X] in
theorem cutoff_test (K : Set X) (hK : IsCompact K) :
    ∃ g : C_c(X, ℝ), (∀ x, 0 ≤ g x) ∧ ∀ x ∈ K, g x = 1 := by
  obtain ⟨g, hg, _, hc, hn⟩ := exists_continuous_one_zero_of_isCompact hK
    isClosed_empty (disjoint_empty K)
  exact ⟨⟨g, hc⟩, fun x => (hn x).1, fun x hx => hg hx⟩

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] in
theorem positive_map_error (L : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    (f h g : C_c(X, ℝ)) (K : Set X) (hf : tsupport f ⊆ K)
    (hh : tsupport h ⊆ K) (hg : ∀ x, 0 ≤ g x) (hg1 : ∀ x ∈ K, g x = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (he : ∀ x, |f x - h x| ≤ ε) :
    |L f - L h| ≤ ε * L g := by
  have hp : f - h ≤ ε • g := by
    intro x
    by_cases hx : x ∈ K
    · simpa [hg1 x hx] using (abs_le.mp (he x)).2
    · have hf0 := image_eq_zero_of_notMem_tsupport (fun H => hx (hf H))
      have hh0 := image_eq_zero_of_notMem_tsupport (fun H => hx (hh H))
      simpa [hf0, hh0] using mul_nonneg hε (hg x)
  have hm : -(ε • g) ≤ f - h := by
    intro x
    by_cases hx : x ∈ K
    · simpa [hg1 x hx] using (abs_le.mp (he x)).1
    · have hf0 := image_eq_zero_of_notMem_tsupport (fun H => hx (hf H))
      have hh0 := image_eq_zero_of_notMem_tsupport (fun H => hx (hh H))
      simpa [hf0, hh0] using neg_nonpos.mpr (mul_nonneg hε (hg x))
  exact abs_le.mpr ⟨by simpa using L.monotone' hm, by simpa using L.monotone' hp⟩

theorem determining_tests_radon_limit
    (X : Type*) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] :
    ∃ tests : ℕ → C_c(X, ℝ), ∀ L : ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ),
      (∀ i, ∃ v : ℝ, Tendsto (fun j => L j (tests i)) atTop (𝓝 v)) →
      ∃ μ : Measure X, IsFiniteMeasureOnCompacts μ ∧ μ.Regular ∧
        ∀ f : C_c(X, ℝ), Tendsto (fun j => L j f) atTop (𝓝 (∫ x, f x ∂μ)) := by
  classical
  let K := CompactExhaustion.choice X
  choose d hd hdense using fun n => supported_dense_tests (K n) (K.isCompact n)
  choose g hg hg1 using fun n => cutoff_test (K n) (K.isCompact n)
  let e := Denumerable.eqv ((ℕ × ℕ) ⊕ ℕ)
  let tests : ℕ → C_c(X, ℝ) := fun i => Sum.elim (fun p => d p.1 p.2) g (e.symm i)
  refine ⟨tests, ?_⟩
  intro L hL
  have hdL (n i : ℕ) : ∃ v : ℝ, Tendsto (fun j => L j (d n i)) atTop (𝓝 v) := by
    simpa [tests] using hL (e (.inl (n,i)))
  have hgL (n : ℕ) : ∃ v : ℝ, Tendsto (fun j => L j (g n)) atTop (𝓝 v) := by
    simpa [tests] using hL (e (.inr n))
  have hc (f : C_c(X, ℝ)) : CauchySeq (fun j => L j f) := by
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact f.hasCompactSupport
    obtain ⟨v, hv⟩ := hgL n
    obtain ⟨C, hC⟩ := hv.bddAbove_range
    let D := max C 1
    have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hDj (j : ℕ) : L j (g n) ≤ D := (hC (mem_range_self j)).trans (le_max_left _ _)
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    let δ := ε / (4*D)
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hD)
    obtain ⟨i, hi⟩ := hdense n f hn δ hδ
    have herr (j : ℕ) : |L j f-L j (d n i)| ≤ ε/4 := by
      have H := positive_map_error (L j) f (d n i) (g n) (K n) hn (hd n i)
        (hg n) (hg1 n) hδ.le (fun x => (hi x).le)
      have hh : δ*D=ε/4 := by dsimp [δ]; field_simp
      exact H.trans ((mul_le_mul_of_nonneg_left (hDj j) hδ.le).trans_eq hh)
    obtain ⟨w, hw⟩ := hdL n i
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hw.cauchySeq (ε/2) (by positivity)
    refine ⟨N, fun j hj k hk => ?_⟩
    have hjk := hN j hj k hk
    rw [Real.dist_eq] at hjk ⊢
    have H := abs_sub_le (L j f) (L j (d n i)) (L k f)
    have H' := abs_sub_le (L j (d n i)) (L k (d n i)) (L k f)
    have he := herr k
    rw [abs_sub_comm] at he
    linarith [herr j]
  choose V hV using fun f : C_c(X, ℝ) => cauchySeq_tendsto_of_complete (hc f)
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀
    { toFun := V
      map_add' := fun f h => by
        apply tendsto_nhds_unique (hV (f+h))
        simpa only [map_add] using (hV f).add (hV h)
      map_smul' := fun r f => by
        apply tendsto_nhds_unique (hV (r • f))
        simpa only [map_smul, smul_eq_mul, RingHom.id_apply] using (hV f).const_mul r }
    (fun f hf => ge_of_tendsto' (hV f) (fun j => (L j).map_nonneg hf))
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, inferInstance, fun f => ?_⟩
  rw [RealRMK.integral_rieszMeasure]
  exact hV f

end ExactSLEMassExtraction

namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped NNReal ENNReal
abbrev UpperPlane := {z : ℂ // 0 < z.im}
noncomputable def upperArea : Measure UpperPlane := volume.comap Subtype.val
noncomputable def actualUpperMass (a q : ℝ) (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) :
    Measure UpperPlane := upperArea.withDensity (fun z => timeMassDensity a q t b z.1)
lemma upperPlane_open : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im

instance upperPlane_locallyCompact : LocallyCompactSpace UpperPlane :=
  upperPlane_open.isOpenEmbedding_subtypeVal.locallyCompactSpace

lemma upper_embedding : MeasurableEmbedding (Subtype.val : UpperPlane → ℂ) :=
  MeasurableEmbedding.subtype_coe upperPlane_open.measurableSet

lemma upper_compact_lower (K : Set UpperPlane) (hK : IsCompact K) :
    ∃ c : ℝ, 0<c ∧ ∀ z∈K, c≤2*z.1.im := by
  by_cases hn : K.Nonempty
  · obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hn
      ((continuous_const.mul (Complex.continuous_im.comp continuous_subtype_val)).continuousOn)
    exact ⟨2*z.1.im, mul_pos (by norm_num) z.2, fun w hw => hmin hw⟩
  · exact ⟨1, by norm_num, fun z hz => False.elim (hn ⟨z,hz⟩)⟩

lemma timeMassDensity_finite (a q : ℝ) (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) (z : ℂ) :
    timeMassDensity a q t b z < ⊤ := by
  apply lt_of_le_of_lt (timeMassDensity_le a q t b z)
  unfold massDensity
  split_ifs <;> simp

lemma timeMassDensity_local_bound (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) (c : ℝ) (hc : 0<c)
    (z : ℂ) (hz : c≤2*z.im) :
    timeMassDensity a q t b z≤ENNReal.ofReal ((c*q)^(-alpha a)) := by
  have hz0 : 0<z.im := by linarith
  have hit := fullRadialDensity_bound a ha z hz0 (2*z.im*q) (by positivity) (by nlinarith) b
  have htar : (2*z.im*q)^(-alpha a)≤(c*q)^(-alpha a) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hc hq) (mul_le_mul_of_nonneg_right hz hq.le)
       (neg_nonpos.mpr (alpha_pos ha).le)
  apply (timeMassDensity_le a q t b z).trans
  simp only [massDensity,ite_eq_left hz0]
  exact ENNReal.ofReal_le_ofReal (hit.2.trans htar)

end ExactSLEGreen
end
end

end OAI
