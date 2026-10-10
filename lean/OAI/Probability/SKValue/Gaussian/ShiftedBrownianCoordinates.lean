import Mathlib
import OAI.Probability.SKValue.Gaussian.BrownianCoordinates
import OAI.Probability.SKValue.Equations.AestronglyMeasurableInitialMax
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
open scoped Topology NNReal BigOperators

noncomputable def shiftedBrownianCoordinates {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (a : ℝ≥0) (T : ℝ) (N : ℕ) (i : Fin N) (ω : Ω) : ℝ :=
  brownianCoordinates (fun r ω ↦ B (a+r) ω-B a ω) (Real.toNNReal (stepSize T N)) N ω i

lemma shiftedBrownianCoordinates_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (a : ℝ≥0)
    {T : ℝ} {N : ℕ} (hT : 0<T) (hN : 0<N) (i : Fin N) :
    HasLaw (shiftedBrownianCoordinates B a T N i) standardGaussian μ := by
  apply brownian_coordinate_hasLaw (hB.shift a)
  exact Real.toNNReal_pos.mpr (div_pos hT (by exact_mod_cast hN))

lemma meshTime_toNNReal {T : ℝ} {N : ℕ} (hT : 0≤T) (j : ℕ) :
    Real.toNNReal (meshTime T N j)=(j : ℝ≥0)*Real.toNNReal (stepSize T N) := by
  have hδ : 0≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  apply NNReal.coe_injective
  unfold meshTime
  rw [Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg j) hδ),
    NNReal.coe_mul,NNReal.coe_natCast,Real.coe_toNNReal _ hδ]

lemma shiftedBrownianCoordinates_exact
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {W : ℝ → Ω → ℝ} {a : ℝ≥0}
    {T : ℝ} {N : ℕ} (hT : 0<T) (hN : 0<N)
    (hW : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ ω,
      W t ω-W s ω=B (a+t.toNNReal) ω-B (a+s.toNNReal) ω)
    (i : Fin N) (ω : Ω) :
    Real.sqrt (stepSize T N)*shiftedBrownianCoordinates B a T N i ω=
      W (meshTime T N (i+1)) ω-W (meshTime T N i) ω := by
  have hδ : 0≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg N)
  have hδ' : 0<Real.toNNReal (stepSize T N) :=
    Real.toNNReal_pos.mpr (div_pos hT (by exact_mod_cast hN))
  rw [hW _ (mesh_time_mem_total hT.le i.isLt.le) _ (mesh_time_mem_total hT.le i.isLt) ω]
  rw [meshTime_toNNReal hT.le,meshTime_toNNReal hT.le]
  have hh := brownian_coordinate_exact (fun r ω ↦ B (a+r) ω-B a ω) hδ' N ω i
  simp only [Real.coe_toNNReal _ hδ] at hh
  change Real.sqrt (stepSize T N)*brownianCoordinates _ _ _ _ _=_
  linarith

lemma GradientStripCore.deriv_bound {T Lu : ℝ} {u : ℝ → ℝ → ℝ}
    (hLu : 0≤Lu) (hLip : ∀ t∈Icc (0 : ℝ) T, ∀ x y, |u t x-u t y|≤Lu*|x-y|)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) T) (x : ℝ) : |deriv (u t) x|≤Lu := by
  have hl : LipschitzWith ⟨Lu,hLu⟩ (u t) :=
    LipschitzWith.of_dist_le_mul (fun y z ↦ by
      change dist (u t y) (u t z)≤Lu*dist y z
      simpa only [Real.dist_eq] using hLip t ht y z)
  have hh := norm_deriv_le_of_lipschitz (x₀:=x) hl
  change ‖deriv (u t) x‖≤Lu at hh
  simpa only [Real.norm_eq_abs] using hh

lemma weighted_pathGradientResidual_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ} {F : Ω → ℝ}
    (hVT : Integrable (fun ω ↦ F ω*u T (X T ω)) μ)
    (hV0 : Integrable (fun ω ↦ F ω*u 0 (X 0 ω)) μ)
    (hLi : ∀ i : Fin N, Integrable (fun ω ↦ F ω*
      (deriv (u (meshTime T N i)) (X (meshTime T N i) ω)*
        (W (meshTime T N (i+1)) ω-W (meshTime T N i) ω))) μ)
    (hQi : ∀ i : Fin N, Integrable (fun ω ↦ F ω*
      (deriv (deriv (u (meshTime T N i))) (X (meshTime T N i) ω)*
        ((W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)^2-stepSize T N))) μ)
    (hL0 : ∀ i : Fin N, (∫ ω, F ω*
      (deriv (u (meshTime T N i)) (X (meshTime T N i) ω)*
        (W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)) ∂μ)=0)
    (hQ0 : ∀ i : Fin N, (∫ ω, F ω*
      (deriv (deriv (u (meshTime T N i))) (X (meshTime T N i) ω)*
        ((W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)^2-stepSize T N)) ∂μ)=0) :
    (∫ ω, F ω*pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω) ∂μ)=
      (∫ ω, F ω*u T (X T ω) ∂μ)-(∫ ω, F ω*u 0 (X 0 ω) ∂μ) := by
  let P := fun i : Fin N ↦ fun ω ↦ F ω*
    (deriv (u (meshTime T N i)) (X (meshTime T N i) ω)*
      (W (meshTime T N (i+1)) ω-W (meshTime T N i) ω))
  let Q := fun i : Fin N ↦ fun ω ↦ F ω*
    (deriv (deriv (u (meshTime T N i))) (X (meshTime T N i) ω)*
      ((W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)^2-stepSize T N))
  have hPi : Integrable (fun ω ↦ ∑ i : Fin N,P i ω) μ := integrable_finsetSum _ (fun i _ ↦ hLi i)
  have hQi' : Integrable (fun ω ↦ ∑ i : Fin N,Q i ω) μ := integrable_finsetSum _ (fun i _ ↦ hQi i)
  have heq (ω : Ω) : F ω*pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)=
      (F ω*u T (X T ω)-F ω*u 0 (X 0 ω)-(∑ i : Fin N,P i ω))-
        (1/2 : ℝ)*(∑ i : Fin N,Q i ω) := by
    simp only [pathGradientResidual,P,Q,mul_sub,Finset.mul_sum,mul_left_comm,mul_comm]
  simp_rw [heq]
  rw [integral_sub (f := fun ω ↦ F ω*u T (X T ω)-F ω*u 0 (X 0 ω)-∑ i : Fin N,P i ω)
    (g := fun ω ↦ (1/2 : ℝ)*(∑ i : Fin N,Q i ω)) ((hVT.sub hV0).sub hPi) (hQi'.const_mul _)]
  rw [integral_sub (f := fun ω ↦ F ω*u T (X T ω)-F ω*u 0 (X 0 ω))
    (g := fun ω ↦ ∑ i : Fin N,P i ω) (hVT.sub hV0) hPi]
  rw [integral_sub hVT hV0,integral_const_mul,
    integral_finsetSum _ (fun i _ ↦ hLi i),integral_finsetSum _ (fun i _ ↦ hQi i)]
  simp only [hL0,hQ0,Finset.sum_const_zero,mul_zero,sub_zero]

end SKValue

end

end OAI
