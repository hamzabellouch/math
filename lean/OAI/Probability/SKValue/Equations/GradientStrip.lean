import Mathlib
import OAI.Probability.SKValue.Equations.ThirdOrderRemainderBound
import OAI.Probability.SKValue.Equations.SumStepsSub

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

structure GradientStrip (T : ℝ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (K L : ℝ) : Prop where
  K_nonneg : 0≤K
  L_nonneg : 0≤L
  gamma_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0≤γ t
  gamma_mono : MonotoneOn γ (Icc (0 : ℝ) T)
  smooth : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 3 (u t)
  bounded : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x|≤1
  second_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |deriv (deriv (u t)) x|≤K
  third_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |iteratedDeriv 3 (u t) x|≤K
  product_bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x*deriv (u t) x|≤K
  second_lipschitz : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x y,
    |deriv (deriv (u s)) y-deriv (deriv (u t)) x|≤L*(|s-t|+|y-x|)
  product_lipschitz : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x y,
    |u s y*deriv (u s) y-u t x*deriv (u t) x|≤L*(|s-t|+|y-x|)
  second_integrable : ∀ x, IntervalIntegrable (fun s ↦ deriv (deriv (u s)) x) volume 0 T
  product_integrable : ∀ x, IntervalIntegrable (fun s ↦ γ s*(u s x*deriv (u s) x)) volume 0 T
  pde : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x,
    u s x-u t x = -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (u r)) x+γ r*(u r x*deriv (u r) x))
  initial : u 0 0=0

lemma mesh_mem_strip_ito {δ T : ℝ} {N j : ℕ} (hδ : 0≤δ)
    (horizon : (N : ℝ)*δ=T) (hj : j≤N) : (j : ℝ)*δ∈Icc (0 : ℝ) T := by
  constructor
  · positivity
  · rw [← horizon]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ

lemma GradientStrip.measurable_second {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (h : GradientStrip T γ u K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    Measurable (deriv (deriv (u t))) := by
  have hc := (h.smooth t ht).continuous_iteratedDeriv 2 (by norm_num)
  simpa only [show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hc.measurable

noncomputable def gradientMeshError (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z, (u T (euler T N γ u z N)-∑ i : Fin N,
    Real.sqrt (stepSize T N)*deriv (u (meshTime T N i)) (euler T N γ u z i)*coordinate N i z)^2
    ∂gaussianProduct (Fin (N+1))

lemma gradientMeshError_nonneg (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) :
    0≤gradientMeshError T N γ u := integral_nonneg (fun _ ↦ sq_nonneg _)

lemma gradientMeshError_bound {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    gradientMeshError T N γ u ≤
      2*((stepSize T N/2)^2*(N : ℝ)*K^2*gaussianSquareVariance)+
      4*(stepSize T N*Real.sqrt (stepSize T N))^2*(N : ℝ)^2*
        cubicEnvelopeMoment (γ T) K ((1/2+γ T)*L)+
      4*(stepSize T N*K*(γ T-γ 0))^2 := by
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
  have hUm (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ u (meshTime T N j) (euler T N γ u z j)) :=
    (h.smooth _ (htime j hj)).continuous.measurable.comp
      (measurable_euler T N γ u (fun k hk ↦ (h.smooth _ (htime k hk.le)).continuous.measurable) j hj)
  have hY (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ euler T N γ u z j) :=
    measurable_euler T N γ u (fun k hk ↦ (h.smooth _ (htime k hk.le)).continuous.measurable) j hj
  have hAm (i : Fin N) : Measurable (fun z ↦ deriv (u (meshTime T N i)) (euler T N γ u z i)) :=
    ((h.smooth _ (htime i i.isLt.le)).continuous_deriv (by norm_num)).measurable.comp (hY i i.isLt.le)
  have hHm (i : Fin N) : Measurable (fun z ↦ deriv (deriv (u (meshTime T N i))) (euler T N γ u z i)) :=
    (h.measurable_second (htime i i.isLt.le)).comp (hY i i.isLt.le)
  have hloc (i : Fin N) (z : Fin (N+1) → ℝ) :
      |u (meshTime T N (i+1)) (euler T N γ u z (i+1))-
        u (meshTime T N i) (euler T N γ u z i)-
        Real.sqrt δ*deriv (u (meshTime T N i)) (euler T N γ u z i)*coordinate N i z-
        (δ/2)*deriv (deriv (u (meshTime T N i))) (euler T N γ u z i)*((coordinate N i z)^2-1)| ≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (coordinate N i z)+
        δ*K*(γ (meshTime T N (i+1))-γ (meshTime T N i)) := by
    let t := meshTime T N i
    have ht : t∈Icc (0 : ℝ) T := htime i i.isLt.le
    have ht' : t+δ∈Icc (0 : ℝ) T := by rw [← hsucc]; exact htime (i+1) (by omega)
    have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht.1 ht'.2
    have hbint (x : ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (u s)) x) volume t (t+δ) := by
      apply (h.second_integrable x).mono_set
      rw [uIcc_of_le hT.le]
      exact uIcc_subset_Icc ht ht'
    have hpint (x : ℝ) : IntervalIntegrable (fun s ↦ γ s*(u s x*deriv (u s) x)) volume t (t+δ) := by
      apply (h.product_integrable x).mono_set
      rw [uIcc_of_le hT.le]
      exact uIcc_subset_Icc ht ht'
    have hh := gradient_euler_one_step (x := euler T N γ u z i) (z := coordinate N i z)
      hδ hδ1 hG h.K_nonneg h.L_nonneg (h.gamma_mono.mono hsub) (h.gamma_nonneg t ht)
      (h.gamma_mono ht htT ht.2) (h.bounded t ht _) (h.smooth t ht)
      (h.second_bound t ht _) (h.third_bound t ht)
      (fun s hs ↦ h.product_bound s (hsub hs))
      (fun s hs y ↦ h.second_lipschitz t ht s (hsub hs) _ y)
      (fun s hs y ↦ h.product_lipschitz t ht s (hsub hs) _ y)
      hbint hpint (h.pde t ht (t+δ) ht')
    dsimp only at hh
    simpa only [hsucc, euler, cubicEnvelope, t, δ, add_assoc, mul_assoc,
      mul_left_comm, mul_comm, div_eq_mul_inv, one_mul] using hh
  have hb := discrete_gradient_residual_L2 (δ := δ) hδ hG h.K_nonneg
    (mul_nonneg (by positivity) h.L_nonneg : 0≤(1/2+γ T)*L)
    (Γ := fun j ↦ γ (meshTime T N j))
    (U := fun j z ↦ u (meshTime T N j) (euler T N γ u z j))
    (A := fun i z ↦ deriv (u (meshTime T N i)) (euler T N γ u z i))
    (H := fun i z ↦ deriv (deriv (u (meshTime T N i))) (euler T N γ u z i))
    (by simpa only [hlast, hzero] using h.gamma_mono ht0 htT hT.le)
    hUm hAm hHm
    (fun i ↦ eulerCoefficient_dependsBefore T i.isLt.le γ u (fun t ↦ deriv (deriv (u t))))
    (fun i z ↦ h.second_bound _ (htime i i.isLt.le) _) hloc
  simpa only [gradientMeshError, hlast, hzero, euler, h.initial,
    sub_zero, δ] using hb

end SKValue

end

end OAI
