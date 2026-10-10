import Mathlib
import OAI.Probability.SKValue.Equations.DriftDefectUniformBound
import OAI.Probability.SKValue.Equations.GradientStripCore

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma GradientStripCore.continuous_second {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (h : GradientStripCore T γ u K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    Continuous (deriv (deriv (u t))) := by
  have hc := (h.smooth t ht).continuous_iteratedDeriv 2 (by norm_num)
  simpa only [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hc

lemma GradientStripCore.continuous_deriv {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (h : GradientStripCore T γ u K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    Continuous (deriv (u t)) := by
  simpa only [iteratedDeriv_one] using (h.smooth t ht).continuous_iteratedDeriv 1 (by norm_num)

lemma pathGradientResidual_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T K L : ℝ} {N : ℕ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    (hT : 0≤T) (h : GradientStripCore T γ u K L)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ) :
    AEStronglyMeasurable (fun ω ↦ pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)) μ := by
  have htime (j : ℕ) (hj : j≤N) := mesh_time_mem_total hT hj
  have hprodA (i : Fin N) : AEStronglyMeasurable (fun ω ↦
      deriv (u (meshTime T N i)) (X (meshTime T N i) ω)*
        (W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)) μ :=
    ((h.continuous_deriv (htime i i.isLt.le)).comp_aestronglyMeasurable
      (hXM _ (htime i i.isLt.le))).mul
      ((hWM _ (htime (i+1) i.isLt)).sub (hWM _ (htime i i.isLt.le)))
  have hprodQ (i : Fin N) : AEStronglyMeasurable (fun ω ↦
      deriv (deriv (u (meshTime T N i))) (X (meshTime T N i) ω)*
        ((W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)^2-stepSize T N)) μ :=
    ((h.continuous_second (htime i i.isLt.le)).comp_aestronglyMeasurable
      (hXM _ (htime i i.isLt.le))).mul
      (((hWM _ (htime (i+1) i.isLt)).sub (hWM _ (htime i i.isLt.le))).pow 2 |>.sub aestronglyMeasurable_const)
  exact ((((h.smooth T ⟨hT,le_rfl⟩).continuous.comp_aestronglyMeasurable (hXM T ⟨hT,le_rfl⟩)).sub
    ((h.smooth 0 ⟨le_rfl,hT⟩).continuous.comp_aestronglyMeasurable (hXM 0 ⟨le_rfl,hT⟩))).sub
      (Finset.aestronglyMeasurable_fun_sum _ (fun i _ ↦ hprodA i))).sub
        ((Finset.aestronglyMeasurable_fun_sum _ (fun i _ ↦ hprodQ i)).const_mul (1/2))

noncomputable def cubicEnvelopeMean (G K C : ℝ) : ℝ :=
  ∫ z : ℝ, cubicEnvelope G K C z ∂standardGaussian

lemma pathGradientResidual_L1_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T K L Lu : ℝ} {N : ℕ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    {Z : Fin N → Ω → ℝ}
    (hT : 0<T) (hT1 : T≤1) (hN : 0<N) (hLu : 0≤Lu)
    (h : GradientStripCore T γ u K L)
    (hLip : ∀ t∈Icc (0 : ℝ) T, ∀ x y, |u t x-u t y|≤Lu*|x-y|)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ)
    (hZlaw : ∀ i, HasLaw (Z i) standardGaussian μ)
    (hZ : ∀ i : Fin N, ∀ ω, Real.sqrt (stepSize T N)*Z i ω=
      W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)
    (hpaths : ∀ᵐ ω ∂μ,
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=W t ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) :
    Integrable (fun ω ↦ pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)) μ ∧
    (∫ ω, |pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)| ∂μ)≤
      Lu*(∫ ω, driftDefect T N γ u (fun t ↦ X t ω) (fun t ↦ W t ω) ∂μ)+
      T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
      stepSize T N*K*(γ T-γ 0) := by
  let D := fun ω ↦ driftDefect T N γ u (fun t ↦ X t ω) (fun t ↦ W t ω)
  let R := fun ω ↦ pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)
  let P := fun i : Fin N ↦ fun ω ↦ cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i ω)
  have hG : 0≤γ T := h.gamma_nonneg T ⟨hT.le,le_rfl⟩
  have hDi : Integrable D μ := (integrable_const (2*T*γ T)).mono'
    (driftDefect_aestronglyMeasurable hT.le (fun t ht ↦ (h.smooth t ht).continuous) hXM hWM)
    (hpaths.mono (fun ω hω ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (driftDefect_nonneg T N γ u _ _)]
      exact driftDefect_uniform_bound hT.le h.gamma_mono (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩)
        h.bounded hω.1 hω.2))
  have hPi (i : Fin N) : Integrable (P i) μ :=
    (cubicEnvelope_memLp_two (hZlaw i) hG K ((1/2+γ T)*L)).integrable (by norm_num)
  have hPint (i : Fin N) : (∫ ω, P i ω ∂μ)=cubicEnvelopeMean (γ T) K ((1/2+γ T)*L) := by
    exact (hZlaw i).integral_comp (measurable_cubicEnvelope _ _ _).aestronglyMeasurable
  let E := fun ω ↦ Lu*D ω+stepSize T N*Real.sqrt (stepSize T N)*(∑ i : Fin N,P i ω)+
    stepSize T N*K*(γ T-γ 0)
  have hEi : Integrable E μ := ((hDi.const_mul Lu).add
    ((integrable_finsetSum _ (fun i _ ↦ hPi i)).const_mul
      (stepSize T N*Real.sqrt (stepSize T N)))).add (integrable_const _)
  have hRE (ω : Ω) : |R ω|≤E ω := pathGradientResidual_bound hT hT1 hN hLu h hLip (fun i ↦ hZ i ω)
  have hRi : Integrable R μ := hEi.mono'
    (pathGradientResidual_aestronglyMeasurable hT.le h hXM hWM)
    (Eventually.of_forall (fun ω ↦ by rw [Real.norm_eq_abs]; exact hRE ω))
  refine ⟨hRi,?_⟩
  calc
    (∫ ω, |R ω| ∂μ)≤∫ ω, E ω ∂μ := integral_mono hRi.abs hEi hRE
    _ = _ := by
      dsimp only [E]
      rw [integral_add
        (f := fun ω ↦ Lu*D ω+stepSize T N*Real.sqrt (stepSize T N)*(∑ i : Fin N,P i ω))
        (g := fun _ ↦ stepSize T N*K*(γ T-γ 0))
        ((hDi.const_mul Lu).add ((integrable_finsetSum _ (fun i _ ↦ hPi i)).const_mul _))
        (integrable_const _),
        integral_add (f := fun ω ↦ Lu*D ω)
          (g := fun ω ↦ stepSize T N*Real.sqrt (stepSize T N)*(∑ i : Fin N,P i ω))
          (hDi.const_mul Lu) ((integrable_finsetSum _ (fun i _ ↦ hPi i)).const_mul _),
        integral_const_mul,integral_const_mul,integral_finsetSum _ (fun i _ ↦ hPi i)]
      simp only [hPint,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        integral_const,probReal_univ,smul_eq_mul,one_mul]
      have hN0 : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
      have hm : (N : ℝ)*stepSize T N=T := by dsimp [stepSize]; field_simp
      dsimp only [D]
      linear_combination (Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L))*hm

end SKValue

namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma pathGradientResidual_L1_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    {Z : (N : ℕ) → Fin N → Ω → ℝ}
    (hT : 0<T) (hT1 : T≤1) (hLu : 0≤Lu)
    (h : GradientStripCore T γ u K L)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ)
    (hZlaw : ∀ N, 0<N → ∀ i, HasLaw (Z N i) standardGaussian μ)
    (hZ : ∀ N, 0<N → ∀ i : Fin N, ∀ ω, Real.sqrt (stepSize T N)*Z N i ω=
      W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=W t ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) :
    Tendsto (fun N ↦ ∫ ω, |pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)| ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  have hD := driftDefect_integral_tendsto hT.le hLu h.gamma_mono
    (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩) h.bounded
    (fun t ht ↦ (h.smooth t ht).continuous) hLip hXM hWM hpaths
  have hs : Tendsto (fun N : ℕ ↦ stepSize T N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have hLim : Tendsto (fun N ↦
      Lu*(∫ ω, driftDefect T N γ u (fun t ↦ X t ω) (fun t ↦ W t ω) ∂μ)+
      T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
      stepSize T N*K*(γ T-γ 0)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero,mul_zero,zero_mul,add_zero,Function.comp_def] using
      ((hD.const_mul Lu).add (((Real.continuous_sqrt.tendsto 0).comp hs).const_mul T |>.mul_const
        (cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)))).add
        ((hs.mul_const K).mul_const (γ T-γ 0))
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ integral_nonneg (fun ω ↦ abs_nonneg _))) _ hLim
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (pathGradientResidual_L1_bound hT hT1 hN hLu h
    (fun t ht x y ↦ by simpa only [sub_self,abs_zero,zero_add] using hLip t ht t ht x y)
    hXM hWM (hZlaw N hN) (hZ N hN) (hpaths.mono (fun _ hh ↦ hh.2))).2

lemma weighted_pathGradientResidual_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T K L Lu H : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    {F : Ω → ℝ} {Z : (N : ℕ) → Fin N → Ω → ℝ}
    (hT : 0<T) (hT1 : T≤1) (hLu : 0≤Lu) (hH : 0≤H)
    (h : GradientStripCore T γ u K L)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ)
    (hZlaw : ∀ N, 0<N → ∀ i, HasLaw (Z N i) standardGaussian μ)
    (hZ : ∀ N, 0<N → ∀ i : Fin N, ∀ ω, Real.sqrt (stepSize T N)*Z N i ω=
      W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=W t ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω))
    (hFm : AEStronglyMeasurable F μ) (hFb : ∀ ω, |F ω|≤H) :
    Tendsto (fun N ↦ ∫ ω, F ω*pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  have hLim := pathGradientResidual_L1_tendsto hT hT1 hLu h hLip hXM hWM hZlaw hZ hpaths
  have hLim' : Tendsto (fun N ↦ H*(∫ ω,
      |pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)| ∂μ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hLim.const_mul H
  apply squeeze_zero_norm' _ hLim'
  filter_upwards [eventually_gt_atTop 0] with N hN
  let R := fun ω ↦ pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)
  have hRi : Integrable R μ := (pathGradientResidual_L1_bound hT hT1 hN hLu h
    (fun t ht x y ↦ by simpa only [sub_self,abs_zero,zero_add] using hLip t ht t ht x y)
    hXM hWM (hZlaw N hN) (hZ N hN) (hpaths.mono (fun _ hh ↦ hh.2))).1
  have hFRi : Integrable (fun ω ↦ F ω*R ω) μ := hRi.bdd_mul hFm
    (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hFb ω))
  rw [Real.norm_eq_abs]
  calc
    |∫ ω, F ω*R ω ∂μ|≤∫ ω, |F ω*R ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, H*|R ω| ∂μ := integral_mono hFRi.abs (hRi.abs.const_mul H) (fun ω ↦ by
      rw [abs_mul]; exact mul_le_mul (hFb ω) le_rfl (abs_nonneg _) hH)
    _ = _ := integral_const_mul _ _

end SKValue

end

end OAI
