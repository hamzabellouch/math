import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.MassVersionsCore
import OAI.Probability.SLEGauge.RadonKernels

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory Filter Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace SLEExactGauge.MassVersions

 

theorem tendsto_finiteMeasure_prod
    {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {l : Filter I} {μ : I → FiniteMeasure X} {ν : I → FiniteMeasure Y}
    {μ₀ : FiniteMeasure X} {ν₀ : FiniteMeasure Y}
    (hμ : Tendsto μ l (𝓝 μ₀)) (hν : Tendsto ν l (𝓝 ν₀)) :
    Tendsto (fun i => (μ i).prod (ν i)) l (𝓝 (μ₀.prod ν₀)) := by
  have hm : Tendsto (fun i => ((μ i).prod (ν i)).mass) l
      (𝓝 (μ₀.mass * ν₀.mass)) := by
    simp only [FiniteMeasure.mass_prod]
    exact hμ.mass.mul hν.mass
  by_cases hμ0 : μ₀ = 0
  · simp only [hμ0, FiniteMeasure.zero_mass, zero_mul] at hm
    simpa only [hμ0, FiniteMeasure.zero_prod] using
      FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hm
  by_cases hν0 : ν₀ = 0
  · simp only [hν0, FiniteMeasure.zero_mass, mul_zero] at hm
    simpa only [hν0, FiniteMeasure.prod_zero] using
      FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hm
  have : Nonempty X := by
    by_contra h
    have : IsEmpty X := not_nonempty_iff.mp h
    exact hμ0 (Subtype.ext (Measure.eq_zero_of_isEmpty _))
  have : Nonempty Y := by
    by_contra h
    have : IsEmpty Y := not_nonempty_iff.mp h
    exact hν0 (Subtype.ext (Measure.eq_zero_of_isEmpty _))
  have hp := ProbabilityMeasure.continuous_prod.tendsto
    (μ₀.normalize, ν₀.normalize) |>.comp
      ((μ₀.tendsto_normalize_of_tendsto hμ hμ0).prodMk_nhds
        (ν₀.tendsto_normalize_of_tendsto hν hν0))
  have he (m : FiniteMeasure X) (n : FiniteMeasure Y) :
      m.prod n = (m.mass * n.mass) •
        (m.normalize.prod n.normalize).toFiniteMeasure := by
    apply Subtype.ext
    change m.toMeasure.prod n.toMeasure =
      (((m.mass * n.mass) • (m.normalize.prod n.normalize).toFiniteMeasure).toMeasure)
    rw [FiniteMeasure.toMeasure_smul]
    change m.toMeasure.prod n.toMeasure =
      (m.mass * n.mass) • (m.normalize.toMeasure.prod n.normalize.toMeasure)
    have hm' := congrArg FiniteMeasure.toMeasure m.self_eq_mass_smul_normalize
    have hn' := congrArg FiniteMeasure.toMeasure n.self_eq_mass_smul_normalize
    simp only [FiniteMeasure.toMeasure_smul,
      ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure] at hm' hn'
    calc
      _ = (m.mass • m.normalize.toMeasure).prod (n.mass • n.normalize.toMeasure) :=
        congrArg₂ Measure.prod hm' hn'
      _ = _ := by rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  simp_rw [he]
  exact (hμ.mass.mul hν.mass).smul
    (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto _ |>.comp hp)

end SLEExactGauge.MassVersions
end
 

 
section
open MeasureTheory Filter Topology Set CompactlySupported
open scoped ENNReal NNReal

namespace SLEExactGauge.MassVersions

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def localizedFinite (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (φ : C_c(X,ℝ≥0)) : FiniteMeasure X :=
  ⟨μ.withDensity (fun x => φ x), isFiniteMeasure_withDensity (by
    rw [lintegral_coe_eq_integral _ (by
      have h : Integrable (fun x => φ.toReal x) μ := φ.toReal.integrable
      simpa only [CompactlySupportedContinuousMap.toReal_apply] using h)]
    exact ENNReal.ofReal_ne_top)⟩

lemma localizedFinite_integral (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (φ : C_c(X,ℝ≥0)) (f : X → ℝ) :
    (∫x, f x ∂localizedFinite μ φ) = ∫x, (φ x:ℝ)*f x ∂μ := by
  exact integral_withDensity_eq_integral_smul φ.continuous.measurable f

 

theorem localizedFinite_tendsto {I : Type*} {l : Filter I}
    (μ : I → Measure X) (μ₀ : Measure X)
    [∀ i, IsFiniteMeasureOnCompacts (μ i)] [IsFiniteMeasureOnCompacts μ₀]
    (h : ∀ f : C_c(X,ℝ), Tendsto (fun i => ∫x,f x∂μ i) l (𝓝 (∫x,f x∂μ₀)))
    (φ : C_c(X,ℝ≥0)) :
    Tendsto (fun i => localizedFinite (μ i) φ) l (𝓝 (localizedFinite μ₀ φ)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let F : C_c(X,ℝ) := f • φ.toReal
  simpa only [localizedFinite_integral, F, CompactlySupportedContinuousMap.smulc_apply,
    smul_eq_mul, CompactlySupportedContinuousMap.toReal_apply, mul_comm] using h F

 
theorem measure_le_of_nonnegative_compact_tests
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (μ ν : Measure X) [IsFiniteMeasureOnCompacts μ] [ν.OuterRegular]
    (h : ∀ f : C_c(X,ℝ), (∀ x, 0≤f x) →
      ENNReal.ofReal (∫x,f x∂μ) ≤ ∫⁻x, ENNReal.ofReal (f x)∂ν) : μ≤ν := by
  have ho (U : Set X) (hU : IsOpen U) : μ U≤ν U := by
    obtain ⟨f,hf,hf0,he⟩ := open_countable_tests U hU
    rw [he μ inferInstance]
    refine iSup_le (fun n => (h (f n) (fun x => (hf n x).1)).trans ?_)
    calc
      _ ≤ ∫⁻x, U.indicator (fun _ => (1:ℝ≥0∞)) x∂ν := by
        apply lintegral_mono
        intro x
        by_cases hx : x∈U
        · simp only [indicator_of_mem hx]
          exact (ENNReal.ofReal_le_ofReal (hf n x).2).trans_eq (by simp)
        · simp [hx, hf0 n hx]
      _ = ν U := by simp [hU.measurableSet]
  intro S
  rw [S.measure_eq_iInf_isOpen ν]
  exact le_iInf (fun U => le_iInf (fun hSU => le_iInf (fun hU =>
    (measure_mono hSU).trans (ho U hU))))

end SLEExactGauge.MassVersions
end
 

 
section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal

namespace SLEExactGauge.MassVersions

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [BorelSpace X]

 

theorem bind_le_of_weak_limit (W : Measure Ω)
    (μ : ℕ → Ω → FiniteMeasure X) (ν : Ω → FiniteMeasure X)
    (hμ : ∀ n, Measurable (μ n)) (hν : Measurable ν)
    (hconv : ∀ᵐ ω ∂W, Tendsto (fun n => μ n ω) atTop (𝓝 (ν ω)))
    (Q : Measure X) [IsFiniteMeasure Q] [Q.OuterRegular]
    (hb : ∀ n, W.bind (fun ω => (μ n ω).toMeasure) ≤ Q) :
    W.bind (fun ω => (ν ω).toMeasure) ≤ Q := by
  have hm (n : ℕ) : Measurable (fun ω => (μ n ω).toMeasure) :=
    measurable_subtype_coe.comp (hμ n)
  have hn : Measurable (fun ω => (ν ω).toMeasure) := measurable_subtype_coe.comp hν
  have ht (f : BoundedContinuousFunction X ℝ≥0) :
      (∫⁻x, (f x : ℝ≥0∞) ∂W.bind (fun ω => (ν ω).toMeasure)) ≤ ∫⁻x, (f x : ℝ≥0∞) ∂Q := by
    have hf : Measurable (fun x => (f x : ℝ≥0∞)) := f.continuous.measurable.coe_nnreal_ennreal
    rw [Measure.lintegral_bind hn.aemeasurable hf.aemeasurable]
    calc
      _ = ∫⁻ω, liminf (fun n => ∫⁻x, (f x : ℝ≥0∞) ∂(μ n ω)) atTop ∂W := by
        apply lintegral_congr_ae
        filter_upwards [hconv] with ω hω
        exact (FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp hω f).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ω, ∫⁻x, (f x : ℝ≥0∞) ∂(μ n ω) ∂W) atTop :=
        lintegral_liminf_le (fun n => (Measure.measurable_lintegral hf).comp (hm n))
      _ ≤ ∫⁻x, (f x : ℝ≥0∞) ∂Q := by
        have hh (n : ℕ) : (∫⁻ω, ∫⁻x, (f x : ℝ≥0∞) ∂(μ n ω) ∂W) ≤ ∫⁻x, (f x : ℝ≥0∞) ∂Q := by
          rw [← Measure.lintegral_bind (hm n).aemeasurable hf.aemeasurable]
          exact lintegral_mono' (hb n) le_rfl
        simpa only [liminf_const] using liminf_le_liminf (f := atTop) (Eventually.of_forall hh)
  have havg : IsFiniteMeasure (W.bind (fun ω => (ν ω).toMeasure)) := by
    constructor
    have h := ht (BoundedContinuousFunction.const X 1)
    simp only [BoundedContinuousFunction.const_apply, ENNReal.coe_one, lintegral_one] at h
    exact h.trans_lt (measure_lt_top Q univ)
  apply measure_le_of_nonnegative_compact_tests
  intro f hf
  rw [ofReal_integral_eq_lintegral_ofReal f.integrable (Eventually.of_forall hf)]
  exact ht f.nnrealPart.toBoundedContinuousFunction

 

theorem average_prod_le_of_weak_limit
    [TopologicalSpace.PseudoMetrizableSpace X]
    (W : Measure Ω) (μ : ℕ → Ω → FiniteMeasure X) (ν : Ω → FiniteMeasure X)
    (hμ : ∀ n, Measurable (μ n)) (hν : Measurable ν)
    (hconv : ∀ᵐ ω ∂W, Tendsto (fun n => μ n ω) atTop (𝓝 (ν ω)))
    (Q : Measure (X × X)) [IsFiniteMeasure Q] [Q.OuterRegular]
    (hb : ∀ n, W.bind (fun ω => (μ n ω).toMeasure.prod (μ n ω).toMeasure) ≤ Q) :
    W.bind (fun ω => (ν ω).toMeasure.prod (ν ω).toMeasure) ≤ Q := by
  apply bind_le_of_weak_limit W
    (fun n ω => (μ n ω).prod (μ n ω)) (fun ω => (ν ω).prod (ν ω))
    (fun n => (FiniteMeasure.measurable_fun_prod.comp ((hμ n).prodMk (hμ n))).subtype_mk)
    ((FiniteMeasure.measurable_fun_prod.comp (hν.prodMk hν)).subtype_mk) _ Q hb
  filter_upwards [hconv] with ω hω
  exact tendsto_finiteMeasure_prod hω hω

 

omit [LocallyCompactSpace X] in
theorem ae_nullSingleton_of_average_prod_diagonal [LocallyCompactSpace X]
    (W : Measure Ω) (ν : Ω → FiniteMeasure X) (hν : Measurable ν)
    (hdiag : W.bind (fun ω => (ν ω).toMeasure.prod (ν ω).toMeasure) (diagonal X) = 0) :
    ∀ᵐ ω ∂W, NullSingletonClass (ν ω).toMeasure := by
  have hm : Measurable (fun ω => (ν ω).toMeasure.prod (ν ω).toMeasure) :=
    FiniteMeasure.measurable_fun_prod.comp (hν.prodMk hν)
  have hd : MeasurableSet (diagonal X) := isClosed_diagonal.measurableSet
  rw [Measure.bind_apply hd hm.aemeasurable] at hdiag
  have hae := (lintegral_eq_zero_iff' ((Measure.measurable_coe hd).comp hm).aemeasurable).mp hdiag
  filter_upwards [hae] with ω hω
  constructor
  intro x
  apply mul_self_eq_zero.mp
  apply le_antisymm _ bot_le
  have hsub : ({x} : Set X) ×ˢ {x} ⊆ diagonal X := by
    rintro p ⟨hp,hq⟩
    simp only [mem_singleton_iff] at hp hq
    exact hp.trans hq.symm
  simpa only [Measure.prod_prod, Pi.zero_apply, bot_eq_zero] using
    (measure_mono (μ := (ν ω).toMeasure.prod (ν ω).toMeasure) hsub).trans_eq hω

 

omit [LocallyCompactSpace X] in
lemma diagonal_null_of_ac_prod [LocallyCompactSpace X]
    (V : Measure X) [SFinite V] [NullSingletonClass V]
    (Q : Measure (X × X)) (hQ : Q ≪ V.prod V) : Q (diagonal X) = 0 := by
  apply hQ
  rw [Measure.prod_apply isClosed_diagonal.measurableSet]
  have he (x : X) : Prod.mk x ⁻¹' diagonal X = {x} := by ext y; simp [diagonal, eq_comm]
  simp_rw [he, measure_singleton, lintegral_zero]

end SLEExactGauge.MassVersions
end
 

 
section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEKernel

 

theorem actual_mixed_density_product_bound (a : ℝ) (ha : 1/4<a) (m : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
    IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W →
    ∀ (x : Fin m → UpperPlane) (c : ℝ), 0<c → (∀ i, c≤2*(x i).1.im) →
    ∀ q : Fin m → ℝ, (∀ i, 0<q i) → (∀ i, q i≤1) → ∀ t : Fin m → ℝ≥0∞,
      (∫⁻ b, ∏ i, timeMassDensity a (q i) (t i) b (x i).1 ∂W) ≤
        ENNReal.ofReal C * kernel (alpha a) c (fun i => (x i).1) := by
  obtain ⟨C,hC,hCb⟩ := actual_density_product_bound a ha m
  refine ⟨C,hC,?_⟩
  intro W hprob hW x c hc hcx q hq hq1 t
  let z : Fin m → ℂ := fun i => (x i).1
  have hz (i) : 0<(z i).im := (x i).2
  apply (lintegral_mono (fun b => Finset.prod_le_prod
    (fun i _ => timeMassDensity_le a (q i) (t i) b (z i)))).trans
  by_cases hinj : Function.Injective z
  · let cap := fun i => cappedDistance c z i
    let target := fun i => 2*(z i).im*q i
    have hcap (i) : 0<cap i := cappedDistance_pos hc z hinj i
    have ht (i) : 0<target i ∧ target i≤2*(z i).im := by
      refine ⟨mul_pos (mul_pos (by norm_num) (hz i)) (hq i),?_⟩
      dsimp [target]
      exact mul_le_of_le_one_right (mul_nonneg (by norm_num) (hz i).le) (hq1 i)
    have hh := hCb W hW z hinj hz cap target
      (fun i => ⟨hcap i,(cappedDistance_le c z i).trans (hcx i)⟩)
      (fun i j hij => by simpa [dist_eq_norm] using cappedDistance_le_dist c z i j hij.symm) ht
    have he (b : ExactSLEGenerator.Driver) (i) : massDensity a (q i) b (z i)=
        ENNReal.ofReal (fullRadialDensity a b.1 (z i) (target i)) := by
      simp [massDensity,hz i,target]
    simp_rw [he]
    have hk : ENNReal.ofReal (C*∏ i, cap i^(-alpha a))=ENNReal.ofReal C*kernel (alpha a) c z := by
      rw [ENNReal.ofReal_mul hC.le,ENNReal.ofReal_prod_of_nonneg
        (fun i _ => Real.rpow_nonneg (hcap i).le _)]
      congr 1
      unfold kernel
      apply Finset.prod_congr rfl
      intro i _
      exact (ENNReal.ofReal_rpow_of_pos (hcap i)).symm
    exact hh.trans_eq hk
  · rw [kernel_top_of_not_injective (alpha a) c (alpha_pos ha) hc z hinj,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hC))]
    exact le_top

 
def pairKernel (α c : ℝ) (p : UpperPlane × UpperPlane) : ℝ≥0∞ :=
  kernel α c (fun i => (MeasurableEquiv.finTwoArrow.symm p i).1)

lemma pairKernel_measurable (α c : ℝ) (hα : 0≤α) : Measurable (pairKernel α c) :=
  (measurable_kernel hα c).comp (by
    apply Measurable.of_eval
    intro i
    exact measurable_subtype_coe.comp
      ((measurable_pi_apply i).comp MeasurableEquiv.finTwoArrow.symm.measurable))

lemma pairKernel_integrable_on_compact (α c : ℝ) (hα : 0<α) (hα1 : α<1)
    (hc : 0<c) (K : Set UpperPlane) (hK : IsCompact K) :
    (∫⁻ p in K ×ˢ K, pairKernel α c p ∂upperArea.prod upperArea) < ∞ := by
  let F : ℂ × ℂ → ℝ≥0∞ := fun p => kernel α c (MeasurableEquiv.finTwoArrow.symm p)
  have hF : Measurable F := (measurable_kernel hα.le c).comp
    MeasurableEquiv.finTwoArrow.symm.measurable
  have he (x y : UpperPlane) : pairKernel α c (x,y)=F (x.1,y.1) := by
    unfold pairKernel F
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [←Measure.prod_restrict,lintegral_prod _ (pairKernel_measurable α c hα.le).aemeasurable]
  simp_rw [he]
  have hsub (x : ℂ) : (∫⁻ y in K, F (x,y.1) ∂upperArea) =
      ∫⁻ y in Subtype.val '' K, F (x,y) :=
    setLIntegral_subtype upperPlane_open.measurableSet K (fun y => F (x,y))
  simp_rw [hsub]
  rw [show (∫⁻ x in K, ∫⁻ y in Subtype.val '' K, F (x.1,y) ∂volume ∂upperArea) =
      ∫⁻ x in Subtype.val '' K, ∫⁻ y in Subtype.val '' K, F (x,y) ∂volume ∂volume from
        setLIntegral_subtype (μ := (volume : Measure ℂ)) upperPlane_open.measurableSet K
          (fun x => ∫⁻y in Subtype.val '' K, F (x,y))]
  rw [←lintegral_prod _ hF.aemeasurable,
    (measurePreserving_finTwoArrow (volume.restrict (Subtype.val '' K))).symm.lintegral_comp
      (measurable_kernel hα.le c)]
  exact capped_distance_kernel_integral α c hα hα1 hc 2 (Subtype.val '' K)
    (hK.image continuous_subtype_val).measurableSet (hK.image continuous_subtype_val).isBounded

instance upperArea_atomless : NullSingletonClass upperArea := by
  constructor
  intro z
  rw [upperArea,upper_embedding.comap_apply]
  simp

end ExactSLEGreen
end
end
 

 
section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal

namespace SLEExactGauge.MassVersions

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

 

lemma average_density_prod_le (W : Measure Ω) [SFinite W]
    (V : Measure X) [SFinite V] (ρ : Ω → X → ℝ≥0∞)
    (hρ : Measurable (Function.uncurry ρ)) (q : X × X → ℝ≥0∞)
    (hb : ∀ x y, (∫⁻ω, ρ ω x * ρ ω y ∂W) ≤ q (x,y)) :
    W.bind (fun ω => (V.withDensity (ρ ω)).prod (V.withDensity (ρ ω))) ≤
      (V.prod V).withDensity q := by
  have hr : Measurable (fun p : Ω × (X × X) => ρ p.1 p.2.1 * ρ p.1 p.2.2) :=
    (hρ.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hρ.comp (measurable_fst.prodMk measurable_snd.snd))
  have he (ω : Ω) : (V.withDensity (ρ ω)).prod (V.withDensity (ρ ω)) =
      (V.prod V).withDensity (fun p => ρ ω p.1 * ρ ω p.2) :=
    prod_withDensity (hρ.comp (measurable_const.prodMk measurable_id))
      (hρ.comp (measurable_const.prodMk measurable_id))
  simp_rw [he]
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.bind_apply hS (measurable_withDensity hr).aemeasurable]
  simp_rw [withDensity_apply _ hS]
  rw [lintegral_lintegral_swap hr.aemeasurable]
  exact lintegral_mono (fun p => hb p.1 p.2)

 
lemma average_localized_density_prod_le [TopologicalSpace X] [BorelSpace X]
    (W : Measure Ω) [SFinite W] (V : Measure X) [SFinite V]
    (ρ : Ω → X → ℝ≥0∞) (hρ : Measurable (Function.uncurry ρ))
    (φ : C_c(X,ℝ≥0)) (q : X × X → ℝ≥0∞)
    (hb : ∀ x∈tsupport φ,∀ y∈tsupport φ,(∫⁻ω,ρ ω x*ρ ω y∂W)≤q (x,y)) :
    W.bind (fun ω => (V.withDensity (fun x => ρ ω x*(φ x:ℝ≥0∞))).prod
      (V.withDensity (fun x => ρ ω x*(φ x:ℝ≥0∞)))) ≤
        (V.prod V).withDensity (fun p => (φ p.1:ℝ≥0∞)*(φ p.2:ℝ≥0∞)*q p) := by
  have hφ : Measurable (fun x => (φ x:ℝ≥0∞)) := φ.continuous.measurable.coe_nnreal_ennreal
  refine average_density_prod_le W V (fun ω x => ρ ω x*(φ x:ℝ≥0∞))
    (hρ.mul (hφ.comp measurable_snd)) _ ?_
  intro x y
  by_cases hx : x∈tsupport φ
  · by_cases hy : y∈tsupport φ
    · have hm : Measurable (fun ω => ρ ω x*ρ ω y) :=
        (hρ.comp (measurable_id.prodMk measurable_const)).mul
          (hρ.comp (measurable_id.prodMk measurable_const))
      have he (ω : Ω) : (ρ ω x*(φ x:ℝ≥0∞))*(ρ ω y*(φ y:ℝ≥0∞)) =
          ((φ x:ℝ≥0∞)*(φ y:ℝ≥0∞))*(ρ ω x*ρ ω y) := by ac_rfl
      simp_rw [he]
      rw [lintegral_const_mul _ hm]
      exact mul_le_mul' le_rfl (hb x hx y hy)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · simp [image_eq_zero_of_notMem_tsupport hx]

 
lemma convex_density_moment_le (W : Measure Ω) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ≥0∞) (hc : ∑i∈s,c i=1)
    (f g : ι → Ω → ℝ≥0∞) (hf : ∀ i∈s,Measurable (f i))
    (hg : ∀ i∈s,Measurable (g i)) (Q : ℝ≥0∞)
    (hb : ∀ i∈s,∀ j∈s,(∫⁻ω,f i ω*g j ω∂W)≤Q) :
    (∫⁻ω,(∑i∈s,c i*f i ω)*(∑i∈s,c i*g i ω)∂W) ≤ Q := by
  have he (ω : Ω) : (∑i∈s,c i*f i ω)*(∑i∈s,c i*g i ω) =
      ∑i∈s,∑j∈s, (c i*c j)*(f i ω*g j ω) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ac_rfl
  simp_rw [he]
  rw [lintegral_finsetSum s (f := fun i ω => ∑j∈s, (c i*c j)*(f i ω*g j ω)) (fun i hi =>
    Finset.measurable_sum s (fun j hj => measurable_const.mul ((hf i hi).mul (hg j hj))))]
  calc
    _ = ∑i∈s,∑j∈s,(c i*c j)*(∫⁻ω,f i ω*g j ω∂W) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [lintegral_finsetSum s (f := fun j ω => (c i*c j)*(f i ω*g j ω)) (fun j hj => measurable_const.mul ((hf i hi).mul (hg j hj)))]
      apply Finset.sum_congr rfl
      intro j hj
      exact lintegral_const_mul _ ((hf i hi).mul (hg j hj))
    _ ≤ ∑i∈s,∑j∈s,(c i*c j)*Q := Finset.sum_le_sum (fun i hi =>
      Finset.sum_le_sum (fun j hj => mul_le_mul' le_rfl (hb i hi j hj)))
    _ = Q := by simp only [←Finset.sum_mul,←Finset.mul_sum,hc,mul_one,one_mul]

lemma measurable_localizedFinite [TopologicalSpace X] [BorelSpace X]
    (μ : Ω → Measure X) [∀ ω, IsFiniteMeasureOnCompacts (μ ω)]
    (hμ : Measurable μ) (φ : C_c(X,ℝ≥0)) :
    Measurable (fun ω => localizedFinite (μ ω) φ) := by
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro S hS
  simp only [withDensity_apply _ hS]
  simp_rw [←lintegral_indicator hS]
  exact (Measure.measurable_lintegral
    (φ.continuous.measurable.coe_nnreal_ennreal.indicator hS)).comp hμ

end SLEExactGauge.MassVersions
end
 

 
section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEKernel SLEExactGauge.MassVersions

def actualConvexMass (a : ℝ) (s : Finset ℕ) (c : ℕ → ℝ)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : Measure UpperPlane :=
  ∑j∈s, ENNReal.ofReal (c j) • actualUpperMass a (Real.exp (-2*a*((j:ℝ)+1))) t b

def actualConvexDensity (a : ℝ) (s : Finset ℕ) (c : ℕ → ℝ)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) (z : UpperPlane) : ℝ≥0∞ :=
  ∑j∈s, ENNReal.ofReal (c j) * timeMassDensity a (Real.exp (-2*a*((j:ℝ)+1))) t b z.1

lemma actualConvexDensity_measurable (a : ℝ) (ha : 1/4<a) (s : Finset ℕ)
    (c : ℕ → ℝ) (t : ℝ≥0∞) :
    Measurable (Function.uncurry (actualConvexDensity a s c t)) := by
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul ((timeMassDensity_measurable a ha _ (Real.exp_pos _)
    (level_step_le_one a ha j) t).comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)))

lemma actualConvexMass_density (a : ℝ) (ha : 1/4<a) (s : Finset ℕ)
    (c : ℕ → ℝ) (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) :
    actualConvexMass a s c t b = upperArea.withDensity (actualConvexDensity a s c t b) := by
  apply Measure.ext
  intro S hS
  simp only [actualConvexMass,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,
    actualUpperMass,withDensity_apply _ hS,actualConvexDensity]
  have hm (j : ℕ) : Measurable (fun z : UpperPlane =>
      timeMassDensity a (Real.exp (-2*a*((j:ℝ)+1))) t b z.1) :=
    (timeMassDensity_measurable a ha _ (Real.exp_pos _) (level_step_le_one a ha j) t).comp
      (measurable_const.prodMk measurable_subtype_coe)
  rw [lintegral_finsetSum s (f := fun j (z : UpperPlane) => ENNReal.ofReal (c j) *
    timeMassDensity a (Real.exp (-2*a*((j:ℝ)+1))) t b z.1)
    (fun j _ => measurable_const.mul (hm j))]
  exact Finset.sum_congr rfl (fun j _ => (lintegral_const_mul _ (hm j)).symm)

lemma actualConvexMass_measurable (a : ℝ) (ha : 1/4<a) (s : Finset ℕ)
    (c : ℕ → ℝ) (t : ℝ≥0∞) : Measurable (actualConvexMass a s c t) := by
  simp_rw [show actualConvexMass a s c t =
    fun b => upperArea.withDensity (actualConvexDensity a s c t b) from
      funext (actualConvexMass_density a ha s c t)]
  exact measurable_withDensity (actualConvexDensity_measurable a ha s c t)

lemma actualConvexMass_finiteOnCompacts (a : ℝ) (ha : 1/4<a) (s : Finset ℕ)
    (c : ℕ → ℝ) (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) :
    IsFiniteMeasureOnCompacts (actualConvexMass a s c t b) := by
  constructor
  intro K hK
  rw [actualConvexMass,Measure.finsetSum_apply]
  apply ENNReal.sum_lt_top.mpr
  intro j _
  have := actualUpperMass_finiteOnCompacts a ha _ (Real.exp_pos _)
    (level_step_le_one a ha j) t b
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

lemma actualConvexMass_integral (a : ℝ) (ha : 1/4<a) (s : Finset ℕ)
    (c : ℕ → ℝ) (hc : ∀ j∈s,0≤c j) (t : ℝ≥0∞)
    (b : ExactSLEGenerator.Driver) (f : C_c(UpperPlane,ℝ)) :
    (∫z,f z∂actualConvexMass a s c t b) =
      ∑j∈s,c j*(∫z,f z∂actualUpperMass a (Real.exp (-2*a*((j:ℝ)+1))) t b) := by
  let (j : ℕ) := actualUpperMass_finiteOnCompacts a ha _ (Real.exp_pos _)
    (level_step_le_one a ha j) t b
  rw [actualConvexMass,integral_finsetSum_measure (fun j _ =>
    f.integrable.smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hc j hj),smul_eq_mul]

lemma actual_pair_density_bound (a : ℝ) (ha : 1/4<a) :
    ∃ C : ℝ,0<C ∧ ∀ (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
    IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W →
    ∀ (x y : UpperPlane) (c : ℝ),0<c → c≤2*x.1.im → c≤2*y.1.im →
    ∀ (q r : ℝ),0<q → q≤1 → 0<r → r≤1 → ∀ (u v : ℝ≥0∞),
      (∫⁻b,timeMassDensity a q u b x.1*timeMassDensity a r v b y.1∂W) ≤
        ENNReal.ofReal C * pairKernel (alpha a) c (x,y) := by
  obtain ⟨C,hC,hb⟩ := actual_mixed_density_product_bound a ha 2
  refine ⟨C,hC,?_⟩
  intro W hprob hW x y c hc hx hy q r hq hq1 hr hr1 u v
  have h := hb W hW (MeasurableEquiv.finTwoArrow.symm (x,y)) c hc
    (by intro i; fin_cases i <;> assumption) ![q,r]
    (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> assumption) ![u,v]
  simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    pairKernel,MeasurableEquiv.finTwoArrow_symm_apply,Fin.cons_zero,Fin.cons_one] using h

 

theorem actualConvexDensity_pair_bound (a : ℝ) (ha : 1/4<a) :
    ∃ C : ℝ,0<C ∧ ∀ (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
    IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W →
    ∀ (s : Finset ℕ) (c : ℕ → ℝ), (∀ j∈s,0≤c j) → (∑j∈s,c j=1) →
    ∀ (t : ℝ≥0∞) (x y : UpperPlane) (d : ℝ),0<d → d≤2*x.1.im → d≤2*y.1.im →
      (∫⁻b,actualConvexDensity a s c t b x*actualConvexDensity a s c t b y∂W) ≤
        ENNReal.ofReal C * pairKernel (alpha a) d (x,y) := by
  obtain ⟨C,hC,hb⟩ := actual_pair_density_bound a ha
  refine ⟨C,hC,?_⟩
  intro W hprob hW s c hc hsum t x y d hd hx hy
  have hc' : ∑ j∈s, ENNReal.ofReal (c j)=1 := by
    rw [←ENNReal.ofReal_sum_of_nonneg hc,hsum,ENNReal.ofReal_one]
  apply convex_density_moment_le W s (fun j => ENNReal.ofReal (c j)) hc'
  · intro j _
    exact (timeMassDensity_measurable a ha _ (Real.exp_pos _)
      (level_step_le_one a ha j) t).comp (measurable_id.prodMk measurable_const)
  · intro j _
    exact (timeMassDensity_measurable a ha _ (Real.exp_pos _)
      (level_step_le_one a ha j) t).comp (measurable_id.prodMk measurable_const)
  · intro i _ j _
    exact hb W hW x y d hd hx hy _ _ (Real.exp_pos _) (level_step_le_one a ha i)
      (Real.exp_pos _) (level_step_le_one a ha j) t t

end ExactSLEGreen
end
end

end OAI
