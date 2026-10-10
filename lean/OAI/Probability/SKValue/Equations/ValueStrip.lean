import Mathlib
import OAI.Probability.SKValue.Equations.GradientErrorConstant
import OAI.Probability.SKValue.Processes.ValueEulerOneStep

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

structure ValueStrip (T : ℝ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ) (K L : ℝ) : Prop where
  K_nonneg : 0≤K
  L_nonneg : 0≤L
  gamma_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0≤γ t
  gamma_mono : MonotoneOn γ (Icc (0 : ℝ) T)
  smooth : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 3 (V t)
  bounded : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |deriv (V t) x|≤1
  second_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |deriv (deriv (V t)) x|≤K
  third_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |iteratedDeriv 3 (V t) x|≤K
  product_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |(1/2 : ℝ)*(deriv (V t) x)^2|≤K
  second_lipschitz : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x y,
    |deriv (deriv (V s)) y-deriv (deriv (V t)) x|≤L*(|s-t|+|y-x|)
  product_lipschitz : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x y,
    |(1/2 : ℝ)*(deriv (V s) y)^2-(1/2 : ℝ)*(deriv (V t) x)^2|≤L*(|s-t|+|y-x|)
  second_integrable : ∀ x, IntervalIntegrable (fun s ↦ deriv (deriv (V s)) x) volume 0 T
  product_integrable : ∀ x, IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) x)^2)) volume 0 T
  pde : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x,
    V s x-V t x = -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (V r)) x+γ r*((1/2 : ℝ)*(deriv (V r) x)^2))

noncomputable def valueMeshEnergy (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ)
    (j : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  ∑ i ∈ Finset.range j, (stepSize T N/2)*γ (meshTime T N i)*
    (deriv (V (meshTime T N i)) (euler T N γ (fun t ↦ deriv (V t)) z i))^2

noncomputable def valueMeshCompensated (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ)
    (j : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  V (meshTime T N j) (euler T N γ (fun t ↦ deriv (V t)) z j)-valueMeshEnergy T N γ V j z

lemma valueMeshCompensated_step (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ)
    (j : ℕ) (z : Fin (N+1) → ℝ) :
    valueMeshCompensated T N γ V (j+1) z-valueMeshCompensated T N γ V j z =
    V (meshTime T N (j+1)) (euler T N γ (fun t ↦ deriv (V t)) z (j+1))-
    V (meshTime T N j) (euler T N γ (fun t ↦ deriv (V t)) z j)-
    (stepSize T N/2)*γ (meshTime T N j)*
      (deriv (V (meshTime T N j)) (euler T N γ (fun t ↦ deriv (V t)) z j))^2 := by
  simp only [valueMeshCompensated, valueMeshEnergy, Finset.sum_range_succ]
  ring

lemma valueMeshCompensated_zero (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ)
    (z : Fin (N+1) → ℝ) : valueMeshCompensated T N γ V 0 z=V 0 0 := by
  simp [valueMeshCompensated, valueMeshEnergy, meshTime, euler]

noncomputable def valueMeshError (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z, (valueMeshCompensated T N γ V N z-V 0 0-∑ i : Fin N,
    Real.sqrt (stepSize T N)*deriv (V (meshTime T N i))
      (euler T N γ (fun t ↦ deriv (V t)) z i)*coordinate N i z)^2
    ∂gaussianProduct (Fin (N+1))

lemma valueMeshError_bound {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    valueMeshError T N γ V ≤
      2*((stepSize T N/2)^2*(N : ℝ)*K^2*gaussianSquareVariance)+
      4*(stepSize T N*Real.sqrt (stepSize T N))^2*(N : ℝ)^2*
        cubicEnvelopeMoment (γ T) K ((1/2+γ T)*L)+
      4*(stepSize T N*K*(γ T-γ 0))^2 := by
  let u := fun t ↦ deriv (V t)
  let δ := stepSize T N
  have hNr : 0<(N : ℝ) := by exact_mod_cast hN
  have hδ : 0≤δ := by dsimp [δ, stepSize]; positivity
  have hδ1 : δ≤1 := by
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
    dsimp [δ, stepSize]
    exact (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hmesh : (N : ℝ)*δ=T := by dsimp [δ, stepSize]; field_simp
  have htime (j : ℕ) (hj : j≤N) : meshTime T N j∈Icc (0 : ℝ) T :=
    mesh_mem_strip_ito hδ hmesh hj
  have ht0 : (0 : ℝ)∈Icc (0 : ℝ) T := ⟨le_rfl,hT.le⟩
  have htT : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hG : 0≤γ T := h.gamma_nonneg T htT
  have hsucc (j : ℕ) : meshTime T N (j+1)=meshTime T N j+δ := by
    dsimp [meshTime, δ]; push_cast; ring
  have hlast : meshTime T N N=T := hmesh
  have hzero : meshTime T N 0=0 := by simp only [meshTime, Nat.cast_zero, zero_mul]
  have huc (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : Continuous (u t) :=
    (h.smooth t ht).continuous_deriv (by norm_num)
  have hY (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ euler T N γ u z j) :=
    measurable_euler T N γ u (fun k hk ↦ (huc _ (htime k hk.le)).measurable) j hj
  have hAm (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ u (meshTime T N j) (euler T N γ u z j)) :=
    (huc _ (htime j hj)).measurable.comp (hY j hj)
  have hUm (j : ℕ) (hj : j≤N) : Measurable (valueMeshCompensated T N γ V j) := by
    apply Measurable.sub ((h.smooth _ (htime j hj)).continuous.measurable.comp (hY j hj))
    apply Finset.measurable_fun_sum
    intro i hi
    exact ((hAm i (le_trans (Finset.mem_range.mp hi).le hj)).pow_const 2).const_mul _
  have hHm (i : Fin N) : Measurable (fun z ↦ deriv (u (meshTime T N i)) (euler T N γ u z i)) := by
    have hc := (h.smooth _ (htime i i.isLt.le)).continuous_iteratedDeriv 2 (by norm_num)
    have hc' : Continuous (deriv (u (meshTime T N i))) := by
      simpa only [u, show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hc
    exact hc'.measurable.comp (hY i i.isLt.le)
  have hloc (i : Fin N) (z : Fin (N+1) → ℝ) :
      |valueMeshCompensated T N γ V (i+1) z-valueMeshCompensated T N γ V i z-
        Real.sqrt δ*u (meshTime T N i) (euler T N γ u z i)*coordinate N i z-
        (δ/2)*deriv (u (meshTime T N i)) (euler T N γ u z i)*((coordinate N i z)^2-1)| ≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (coordinate N i z)+
        δ*K*(γ (meshTime T N (i+1))-γ (meshTime T N i)) := by
    let t := meshTime T N i
    have ht : t∈Icc (0 : ℝ) T := htime i i.isLt.le
    have ht' : t+δ∈Icc (0 : ℝ) T := by rw [← hsucc]; exact htime (i+1) (by omega)
    have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht.1 ht'.2
    have hbint (x : ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (V s)) x) volume t (t+δ) := by
      apply (h.second_integrable x).mono_set
      rw [uIcc_of_le hT.le]
      exact uIcc_subset_Icc ht ht'
    have hpint (x : ℝ) : IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) x)^2)) volume t (t+δ) := by
      apply (h.product_integrable x).mono_set
      rw [uIcc_of_le hT.le]
      exact uIcc_subset_Icc ht ht'
    have hh := value_euler_one_step (x := euler T N γ u z i) (z := coordinate N i z)
      hδ hδ1 hG h.K_nonneg h.L_nonneg (h.gamma_mono.mono hsub) (h.gamma_nonneg t ht)
      (h.gamma_mono ht htT ht.2) (h.bounded t ht _) (h.smooth t ht)
      (h.second_bound t ht _) (h.third_bound t ht)
      (fun s hs ↦ h.product_bound s (hsub hs))
      (fun s hs y ↦ h.second_lipschitz t ht s (hsub hs) _ y)
      (fun s hs y ↦ h.product_lipschitz t ht s (hsub hs) _ y)
      hbint hpint (h.pde t ht (t+δ) ht')
    dsimp only at hh
    rw [valueMeshCompensated_step]
    convert hh using 1 <;> simp only [hsucc, euler, cubicEnvelope, t, δ, u]
    all_goals congr 1
    all_goals ring_nf
  have hb := discrete_gradient_residual_L2 (δ := δ) hδ hG h.K_nonneg
    (mul_nonneg (by positivity) h.L_nonneg : 0≤(1/2+γ T)*L)
    (Γ := fun j ↦ γ (meshTime T N j))
    (U := valueMeshCompensated T N γ V)
    (A := fun i z ↦ u (meshTime T N i) (euler T N γ u z i))
    (H := fun i z ↦ deriv (u (meshTime T N i)) (euler T N γ u z i))
    (by simpa only [hlast, hzero] using h.gamma_mono ht0 htT hT.le)
    hUm (fun i ↦ hAm i i.isLt.le) hHm
    (fun i ↦ eulerCoefficient_dependsBefore T i.isLt.le γ u (fun t ↦ deriv (u t)))
    (fun i z ↦ h.second_bound _ (htime i i.isLt.le) _) hloc
  simpa only [valueMeshError, valueMeshCompensated_zero, hlast, hzero, u, δ] using hb

lemma valueMeshError_bound_linear {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    valueMeshError T N γ V ≤ stepSize T N*gradientErrorConstant T K L γ := by
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hδ : 0≤ stepSize T N := div_nonneg hT.le hNr.le
  have hδ1 : stepSize T N≤1 := (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hm : (N:ℝ)*stepSize T N=T := by unfold stepSize; field_simp
  exact (valueMeshError_bound hT hT1 h hN).trans (gaussian_mesh_bound_linear hδ hδ1 hm)

lemma valueMeshError_tendsto_zero {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) :
    Tendsto (fun N ↦ valueMeshError T N γ V) atTop (𝓝 0) := by
  have hbound : ∀ᶠ N in atTop,
      valueMeshError T N γ V ≤ stepSize T N*gradientErrorConstant T K L γ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact valueMeshError_bound_linear hT hT1 h hN
  have hlim : Tendsto (fun N ↦ stepSize T N*gradientErrorConstant T K L γ) atTop (𝓝 0) := by
    simpa only [stepSize, zero_mul] using
      (tendsto_const_div_atTop_nhds_zero_nat T).mul_const (gradientErrorConstant T K L γ)
  exact squeeze_zero' (Eventually.of_forall (fun N ↦ integral_nonneg (fun _ ↦ sq_nonneg _))) hbound hlim

end SKValue

end

end OAI
