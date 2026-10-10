import Mathlib
import OAI.Probability.SKValue.Processes.EulerMemLp
import OAI.Probability.SKValue.Equations.CubicEnvelopeMean
import OAI.Probability.SKValue.Gaussian.ShiftedBrownianCoordinates
import OAI.Probability.SKValue.Control.Verification
import OAI.Probability.SKValue.Control.Controls

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma ValueStrip.continuous_second {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : ValueStrip T γ V K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    Continuous (deriv (deriv (V t))) := by
  have hc := (h.smooth t ht).continuous_iteratedDeriv 2 (by norm_num)
  simpa only [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hc

theorem ValueStrip.progressive_control_upper
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) (hγM : Measurable γ)
    {α : ℝ≥0 → Ω → ℝ} (hα : IsProgressive (Filtration.natural B hBm) α)
    (hαb : ∀ s ω, |α s ω|≤1) (x : ℝ) :
    (∫ ω, V T (controlState B γ α x T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω ∂μ)≤V 0 x := by
  let X := controlState B γ α x
  let W := fun t : ℝ ↦ B (Real.toNNReal t)
  let F := fun ω ↦ V T (X T ω)-V 0 (X 0 ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω
  have hγb (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : |γ t|≤γ T := by
    rw [abs_of_nonneg (h.gamma_nonneg t ht)]
    exact h.gamma_mono ht ⟨hT.le,le_rfl⟩ ht.2
  have hiγ : IntervalIntegrable γ volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hT.le]
    exact h.gamma_mono
  have hXm (t : ℝ) (ht : t∈Icc (0 : ℝ) T) :
      StronglyMeasurable[Filtration.natural B hBm (Real.toNNReal t)] (X t) :=
    controlState_past_measurable hBm hα hγM x ht.1
  have hXlp (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : MemLp (X t) 2 μ :=
    controlState_memLp_two hB hBm hα hαb hγM hγb x ht.1 ht.2
  have hVi (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : Integrable (fun ω ↦ V t (X t ω)) μ :=
    (h.value_memLp ht (hXlp t ht)).integrable (by norm_num)
  have hAi : Integrable (controlAccum γ α 2 T) μ :=
    controlAccum_integrable hα hαb hγM hγb 2 hT.le le_rfl
  have hV0 := hVi 0 ⟨le_rfl,hT.le⟩
  have hVT := hVi T ⟨hT.le,le_rfl⟩
  have hFi : Integrable F μ := (hVT.sub hV0).sub (hAi.const_mul _)
  have hW (s : ℝ) (_ : s∈Icc (0 : ℝ) T) (t : ℝ) (_ : t∈Icc (0 : ℝ) T) (ω : Ω) :
      W t ω-W s ω=B (0+t.toNNReal) ω-B (0+s.toNNReal) ω := by simp only [W,zero_add]
  have hbound (N : ℕ) (hN : 0<N) : (∫ ω, F ω ∂μ)≤
      T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
      2*stepSize T N*K*(γ T-γ 0) := by
    let δ := stepSize T N
    let τ := fun j : ℕ ↦ (meshTime T N j).toNNReal
    let D := fun i : Fin N ↦ fun ω ↦ W (meshTime T N (i+1)) ω-W (meshTime T N i) ω
    let H := fun i : Fin N ↦ fun ω ↦ deriv (V (meshTime T N i)) (X (meshTime T N i) ω)
    let A := fun i : Fin N ↦ fun ω ↦ deriv (deriv (V (meshTime T N i))) (X (meshTime T N i) ω)
    let P := fun i : Fin N ↦ fun ω ↦ H i ω*D i ω
    let Q := fun i : Fin N ↦ fun ω ↦ A i ω*(D i ω^2-δ)
    let Z := shiftedBrownianCoordinates B 0 T N
    let E := fun i : Fin N ↦ fun ω ↦ cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i ω)
    have hδ : 0≤δ := div_nonneg hT.le (Nat.cast_nonneg N)
    have htime (j : ℕ) (hj : j≤N) := mesh_time_mem_total hT.le hj
    have hτ (i : Fin N) : τ i≤τ (i+1) := by
      apply Real.toNNReal_mono
      dsimp [meshTime]
      push_cast
      nlinarith
    have hτdiff (i : Fin N) : (τ (i+1) : ℝ)-(τ i : ℝ)=δ := by
      dsimp only [τ]
      rw [Real.coe_toNNReal _ (htime (i+1) i.isLt).1,Real.coe_toNNReal _ (htime i i.isLt.le).1]
      dsimp [meshTime,δ]
      push_cast
      ring
    have hHm (i : Fin N) : StronglyMeasurable[Filtration.natural B hBm (τ i)] (H i) :=
      ((h.smooth _ (htime i i.isLt.le)).continuous_deriv (by norm_num)).comp_stronglyMeasurable
        (hXm _ (htime i i.isLt.le))
    have hAm (i : Fin N) : StronglyMeasurable[Filtration.natural B hBm (τ i)] (A i) :=
      (h.continuous_second (htime i i.isLt.le)).comp_stronglyMeasurable (hXm _ (htime i i.isLt.le))
    have hHi (i : Fin N) : Integrable (H i) μ := by
      apply Integrable.of_bound ((hHm i).mono (Filtration.le _ _)).aestronglyMeasurable 1
      exact Eventually.of_forall (fun ω ↦ by
        simpa only [Real.norm_eq_abs] using h.bounded _ (htime i i.isLt.le) (X _ ω))
    have hAii (i : Fin N) : Integrable (A i) μ := by
      apply Integrable.of_bound ((hAm i).mono (Filtration.le _ _)).aestronglyMeasurable K
      exact Eventually.of_forall (fun ω ↦ by
        simpa only [Real.norm_eq_abs] using h.second_bound _ (htime i i.isLt.le) (X _ ω))
    have hPi (i : Fin N) : Integrable (P i) μ :=
      brownian_predictable_increment_integrable hB hBm (hτ i) (hHm i) (hHi i)
    have hQi (i : Fin N) : Integrable (Q i) μ := by
      simpa only [Q,D,W,hτdiff] using
        brownian_predictable_quadratic_integrable hB hBm (hτ i) (hAm i) (hAii i)
    have hP0 (i : Fin N) : (∫ ω, P i ω ∂μ)=0 :=
      brownian_predictable_increment_mean hB hBm (hτ i) (hHm i)
    have hQ0 (i : Fin N) : (∫ ω, Q i ω ∂μ)=0 := by
      simpa only [Q,D,W,hτdiff] using brownian_predictable_quadratic_mean hB hBm (hτ i) (hAm i)
    have hZlaw (i : Fin N) : HasLaw (Z i) standardGaussian μ :=
      shiftedBrownianCoordinates_hasLaw hB 0 hT hN i
    have hEi (i : Fin N) : Integrable (E i) μ :=
      (cubicEnvelope_memLp_two (hZlaw i) (h.gamma_nonneg T ⟨hT.le,le_rfl⟩)
        K ((1/2+γ T)*L)).integrable (by norm_num)
    have hEmean (i : Fin N) : (∫ ω, E i ω ∂μ)=cubicEnvelopeMean (γ T) K ((1/2+γ T)*L) :=
      (hZlaw i).integral_comp (measurable_cubicEnvelope _ _ _).aestronglyMeasurable
    let R := fun ω ↦ F ω-(∑ i : Fin N, P i ω)-(1/2 : ℝ)*(∑ i : Fin N, Q i ω)
    let J := fun ω ↦ δ*Real.sqrt δ*(∑ i : Fin N, E i ω)+2*δ*K*(γ T-γ 0)
    have hPs : Integrable (fun ω ↦ ∑ i : Fin N, P i ω) μ := integrable_finsetSum _ (fun i _ ↦ hPi i)
    have hQs : Integrable (fun ω ↦ ∑ i : Fin N, Q i ω) μ := integrable_finsetSum _ (fun i _ ↦ hQi i)
    have hEs : Integrable (fun ω ↦ ∑ i : Fin N, E i ω) μ := integrable_finsetSum _ (fun i _ ↦ hEi i)
    have hRi : Integrable R μ := (hFi.sub hPs).sub (hQs.const_mul _)
    have hJi : Integrable J μ := (hEs.const_mul _).add (integrable_const _)
    have hRJ (ω : Ω) : R ω≤J ω := by
      have h1 := controlAccum_integrand_intervalIntegrable hα hαb hγM hiγ hT.le 1 ω
      simp only [pow_one] at h1
      have hh := h.control_mesh_bound (x := x) (X := fun t ↦ X t ω) (W := fun t ↦ W t ω)
        (Z := fun i ↦ Z i ω) hT hT1 hN (fun s _ ↦ hαb _ ω) h1
        (controlAccum_integrand_intervalIntegrable hα hαb hγM hiγ hT.le 2 ω)
        (fun t _ ↦ by simp only [X,controlState,controlAccum,W,pow_one])
        (fun i ↦ shiftedBrownianCoordinates_exact hT hN hW i ω)
      exact hh
    have hRmean : (∫ ω, R ω ∂μ)=(∫ ω, F ω ∂μ) := by
      dsimp only [R]
      rw [integral_sub (f := fun ω ↦ F ω-∑ i : Fin N, P i ω)
        (g := fun ω ↦ (1/2 : ℝ)*(∑ i : Fin N, Q i ω))
        (hFi.sub hPs) (hQs.const_mul (1/2)),integral_sub hFi hPs,integral_const_mul,
        integral_finsetSum _ (fun i _ ↦ hPi i),integral_finsetSum _ (fun i _ ↦ hQi i)]
      simp only [hP0,hQ0,Finset.sum_const_zero,mul_zero,sub_zero]
    have hJmean : (∫ ω, J ω ∂μ)=
        T*Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+2*δ*K*(γ T-γ 0) := by
      dsimp only [J]
      rw [integral_add (hEs.const_mul _) (integrable_const _),integral_const_mul,
        integral_finsetSum _ (fun i _ ↦ hEi i)]
      simp only [hEmean,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        integral_const,probReal_univ,smul_eq_mul,one_mul]
      have hN0 : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
      have hm : (N : ℝ)*δ=T := by dsimp [δ,stepSize]; field_simp
      linear_combination (Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L))*hm
    rw [←hRmean,←hJmean]
    exact integral_mono hRi hJi hRJ
  have hs : Tendsto (fun N : ℕ ↦ stepSize T N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have hlim : Tendsto (fun N ↦
      T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
      2*stepSize T N*K*(γ T-γ 0)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,Real.sqrt_zero,mul_zero,zero_mul,add_zero] using
      ((((Real.continuous_sqrt.tendsto 0).comp hs).const_mul T).mul_const
        (cubicEnvelopeMean (γ T) K ((1/2+γ T)*L))).add
        (((hs.const_mul 2).mul_const K).mul_const (γ T-γ 0))
  have hFle : (∫ ω, F ω ∂μ)≤0 := ge_of_tendsto hlim
    ((eventually_gt_atTop 0).mono (fun N hN ↦ hbound N hN))
  have h0 : (∫ ω, V 0 (X 0 ω) ∂μ)=V 0 x := by
    rw [integral_congr_ae ((controlState_initial hB γ α x).mono (fun ω hω ↦ congrArg (V 0) hω))]
    simp
  dsimp only [F] at hFle
  rw [integral_sub (f := fun ω ↦ V T (X T ω)-V 0 (X 0 ω))
    (g := fun ω ↦ (1/2 : ℝ)*controlAccum γ α 2 T ω)
    (hVT.sub hV0) (hAi.const_mul (1/2)),integral_sub hVT hV0,h0] at hFle
  rw [integral_sub hVT (hAi.const_mul (1/2))]
  linarith

end SKValue

end

end OAI
