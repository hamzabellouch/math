import Mathlib
import OAI.Probability.SKValue.Equations.BrownianIncrementIndepPast

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

structure GradientStripCore (T : ℝ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (K L : ℝ) : Prop where
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

lemma GradientStrip.toCore {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (h : GradientStrip T γ u K L) : GradientStripCore T γ u K L :=
  ⟨h.K_nonneg,h.L_nonneg,h.gamma_nonneg,h.gamma_mono,h.smooth,h.bounded,
    h.second_bound,h.third_bound,h.product_bound,h.second_lipschitz,
    h.product_lipschitz,h.second_integrable,h.product_integrable,h.pde⟩

noncomputable def pathGradientResidual (T : ℝ) (N : ℕ) (u : ℝ → ℝ → ℝ)
    (X W : ℝ → ℝ) : ℝ :=
  u T (X T)-u 0 (X 0)-∑ i : Fin N,
    deriv (u (meshTime T N i)) (X (meshTime T N i))*
      (W (meshTime T N (i+1))-W (meshTime T N i))-
    (1/2 : ℝ)*∑ i : Fin N,
      deriv (deriv (u (meshTime T N i))) (X (meshTime T N i))*
        ((W (meshTime T N (i+1))-W (meshTime T N i))^2-stepSize T N)

lemma pathGradientResidual_bound {T K L Lu : ℝ} {N : ℕ} {γ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} {X W : ℝ → ℝ} {Z : Fin N → ℝ}
    (hT : 0<T) (hT1 : T≤1) (hN : 0<N) (_hLu : 0≤Lu)
    (h : GradientStripCore T γ u K L)
    (hLip : ∀ t∈Icc (0 : ℝ) T, ∀ x y, |u t x-u t y|≤Lu*|x-y|)
    (hZ : ∀ i : Fin N, Real.sqrt (stepSize T N)*Z i=
      W (meshTime T N (i+1))-W (meshTime T N i)) :
    |pathGradientResidual T N u X W|≤Lu*driftDefect T N γ u X W+
      stepSize T N*Real.sqrt (stepSize T N)*
        (∑ i : Fin N, cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i))+
      stepSize T N*K*(γ T-γ 0) := by
  let δ := stepSize T N
  have hNr : 0<(N : ℝ) := by exact_mod_cast hN
  have hδ : 0≤δ := div_nonneg hT.le hNr.le
  have hδ1 : δ≤1 := by
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
    exact (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hmesh : (N : ℝ)*δ=T := by dsimp [δ,stepSize]; field_simp
  have ht0 : (0 : ℝ)∈Icc (0 : ℝ) T := ⟨le_rfl,hT.le⟩
  have htT : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have htime (j : ℕ) (hj : j≤N) : meshTime T N j∈Icc (0 : ℝ) T :=
    mesh_mem_strip_ito hδ hmesh hj
  have hsucc (j : ℕ) : meshTime T N (j+1)=meshTime T N j+δ := by
    dsimp [meshTime,δ]; push_cast; ring
  have hlast : meshTime T N N=T := hmesh
  have hzero : meshTime T N 0=0 := by simp only [meshTime,Nat.cast_zero,zero_mul]
  have hG : 0≤γ T := h.gamma_nonneg T htT
  let D := fun i : Fin N ↦ W (meshTime T N (i+1))-W (meshTime T N i)
  let R := fun i : Fin N ↦ u (meshTime T N (i+1)) (X (meshTime T N (i+1)))-
    u (meshTime T N i) (X (meshTime T N i))-
    deriv (u (meshTime T N i)) (X (meshTime T N i))*D i-
    (1/2 : ℝ)*deriv (deriv (u (meshTime T N i))) (X (meshTime T N i))*(D i^2-δ)
  let E := fun i : Fin N ↦ |X (meshTime T N (i+1))-X (meshTime T N i)-D i-
    δ*γ (meshTime T N i)*u (meshTime T N i) (X (meshTime T N i))|
  have hlocal (i : Fin N) : |R i|≤Lu*E i+
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i)+
      δ*K*(γ (meshTime T N (i+1))-γ (meshTime T N i)) := by
    let t := meshTime T N i
    have ht : t∈Icc (0 : ℝ) T := htime i i.isLt.le
    have ht' : t+δ∈Icc (0 : ℝ) T := by rw [←hsucc]; exact htime (i+1) (by omega)
    have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht.1 ht'.2
    have hbint (x : ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (u s)) x) volume t (t+δ) :=
      intervalIntegrable_substrip hT.le (h.second_integrable x) ht ht'
    have hpint (x : ℝ) : IntervalIntegrable (fun s ↦ γ s*(u s x*deriv (u s) x)) volume t (t+δ) :=
      intervalIntegrable_substrip hT.le (h.product_integrable x) ht ht'
    have hh := gradient_euler_one_step (x:=X t) (z:=Z i) hδ hδ1 hG h.K_nonneg h.L_nonneg
      (h.gamma_mono.mono hsub) (h.gamma_nonneg t ht) (h.gamma_mono ht htT ht.2)
      (h.bounded t ht _) (h.smooth t ht) (h.second_bound t ht _) (h.third_bound t ht)
      (fun s hs ↦ h.product_bound s (hsub hs))
      (fun s hs y ↦ h.second_lipschitz t ht s (hsub hs) _ y)
      (fun s hs y ↦ h.product_lipschitz t ht s (hsub hs) _ y)
      hbint hpint (h.pde t ht (t+δ) ht')
    dsimp only at hh
    have hd : (D i)^2=δ*(Z i)^2 := by
      change (W _-W _)^2=_
      rw [←hZ i,mul_pow,Real.sq_sqrt hδ]
    have hh' : |u (t+δ) (X t+(D i+δ*γ t*u t (X t)))-u t (X t)-
        deriv (u t) (X t)*D i-(1/2 : ℝ)*deriv (deriv (u t)) (X t)*(D i^2-δ)|≤
        δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i)+
          δ*K*(γ (t+δ)-γ t) := by
      have hZd : Real.sqrt δ*Z i=D i := hZ i
      have heq : (1/2 : ℝ)*deriv (deriv (u t)) (X t)*(δ*(Z i)^2-δ)=
          (1/2 : ℝ)*δ*deriv (deriv (u t)) (X t)*((Z i)^2-1) := by ring
      rw [←hZd,mul_pow,Real.sq_sqrt hδ,heq]
      simpa only [cubicEnvelope,mul_assoc] using hh
    have hlu := hLip (t+δ) ht' (X (t+δ)) (X t+(D i+δ*γ t*u t (X t)))
    have he : |X (t+δ)-(X t+(D i+δ*γ t*u t (X t)))|=E i := by
      dsimp only [E,t]
      rw [hsucc]
      congr 1
      ring
    rw [he] at hlu
    have hdecomp : R i=(u (t+δ) (X (t+δ))-
        u (t+δ) (X t+(D i+δ*γ t*u t (X t))))+
        (u (t+δ) (X t+(D i+δ*γ t*u t (X t)))-u t (X t)-
          deriv (u t) (X t)*D i-(1/2 : ℝ)*deriv (deriv (u t)) (X t)*(D i^2-δ)) := by
      dsimp only [R,t]
      rw [hsucc]
      ring
    rw [hdecomp]
    have hn := (abs_add_le _ _).trans (add_le_add hlu hh')
    simpa only [t,←hsucc,add_assoc] using hn
  have hsumEq : pathGradientResidual T N u X W=∑ i : Fin N, R i := by
    dsimp only [pathGradientResidual,R,D]
    rw [sum_local_residual (fun j ↦ u (meshTime T N j) (X (meshTime T N j)))]
    rw [hlast,hzero,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsumEq]
  calc
    _ ≤ ∑ i : Fin N, |R i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, (Lu*E i+δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i)+
      δ*K*(γ (meshTime T N (i+1))-γ (meshTime T N i))) := Finset.sum_le_sum (fun i _ ↦ hlocal i)
    _ = _ := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum]
      rw [sum_steps_sub (fun j ↦ γ (meshTime T N j)),hlast,hzero]
      rfl

end SKValue

end

end OAI
