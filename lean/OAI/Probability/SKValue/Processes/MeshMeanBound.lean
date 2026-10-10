import Mathlib
import OAI.Probability.SKValue.Equations.ShiftedPairing
import OAI.Probability.SKValue.Evolution.UniformGridRiemannBound
import OAI.Probability.SKValue.Processes.MeshRaw

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
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma mesh_mean_bound {T D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    |∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1))|≤D := by
  have := gaussianProduct_probability (Fin (N+1))
  simpa [Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const (μ := gaussianProduct (Fin (N+1)))
      (Eventually.of_forall (fun z ↦ show ‖meshRaw T N γ u j z‖≤D from by
        simpa only [Real.norm_eq_abs, meshRaw] using hD _ (mesh_time_mem hT hN hj) _)))

lemma product_perturbation_bound {a b f D r : ℝ} (hD : 0≤D) (_ : 0≤r)
    (ha : |a|≤D) (hb : |b-1|≤r) (hf : |a-f|≤r) : |a*b-f|≤(D+1)*r := by
  calc
    |a*b-f| = |a*(b-1)+(a-f)| := by congr 1; ring
    _ ≤ |a*(b-1)|+|a-f| := abs_add_le _ _
    _ ≤ D*r+r := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul ha hb (abs_nonneg _) hD) hf
    _ = _ := by ring

theorem finiteGaussian_from_strip_and_moments
    {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {f : ℝ → ℝ} {r : ℕ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L) (hD0 : 0≤D)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hr : ∀ N, 0≤r N)
    (hr0 : Tendsto r atTop (𝓝 0))
    (hq : ∀ N, 0<N → ∀ j : Fin N,
      |(∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1)))-1|≤r N)
    (hm : ∀ N, 0<N → ∀ j : Fin N,
      |(∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1)))-f (meshTime T N j)|≤r N) :
    (∀ᶠ N in atTop, ∀ j<N, 0<predictableNormalizer (meshRaw T N γ u j)
      (gaussianProduct (Fin (N+1)))) ∧
    Tendsto (fun N ↦ finiteShiftedValue T N γ u) atTop (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  let q (N j : ℕ) := ∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1))
  have hqpos : ∀ᶠ N in atTop, ∀ j<N, 0<q N j :=
    uniform_moment_positive hr0 (fun N j hj ↦ hq N (by omega) ⟨j,hj⟩)
  constructor
  · filter_upwards [hqpos] with N hN j hj
    exact predictableNormalizer_pos (hN j hj)
  · let A (N : ℕ) (i : Fin (N+1)) := meshA T (N+1) γ u i
    let B (N : ℕ) (i : Fin (N+1)) := meshB T (N+1) γ u i
    let α (N : ℕ) (i : Fin (N+1)) := Real.sqrt (stepSize T (N+1))/
      predictableNormalizer (meshRaw T (N+1) γ u i) (gaussianProduct (Fin ((N+1)+1)))
    let β (N : ℕ) (i : Fin (N+1)) := Real.sqrt (stepSize T (N+1))*
      ∫ z, meshRaw T (N+1) γ u i z ∂gaussianProduct (Fin ((N+1)+1))
    let bstar (N : ℕ) := meshB T (N+1) γ u (N+1)
    let e (N : ℕ) := gradientMeshError T (N+1) γ u
    let rend (N : ℕ) := Real.sqrt (stepSize T (N+1))*D
    have hproj : ∀ᶠ N in atTop,
        (∑ i, (A N i-α N i)^2)≤e N ∧ (∑ i, (B N i-β N i)^2)≤e N := by
      filter_upwards [(tendsto_add_atTop_nat 1).eventually hqpos] with N hN
      exact mesh_coefficient_errors hT.le h hD (Nat.succ_pos N) (fun i ↦ hN i i.isLt)
    have hnorm (N : ℕ) : (∑ i, (B N i)^2)≤1 ∧ |bstar N|≤1 :=
      mesh_coefficients_norms hT.le h (Nat.succ_pos N)
    have hαnorm (N : ℕ) : (∑ i, (α N i)^2)≤(Real.sqrt T*D)^2 :=
      mesh_leading_norm hT.le h hD0 hD (Nat.succ_pos N)
    have hend (N : ℕ) : |α N (Fin.last N)|≤rend N := by
      have := gaussianProduct_probability (Fin ((N+1)+1))
      exact sqrt_div_normalizer_bound
        (mesh_raw_memLp hT.le h hD (Nat.succ_pos N) (Nat.le_succ N)) hD0
        (Eventually.of_forall (fun z ↦ hD _ (mesh_time_mem hT.le (Nat.succ_pos N) (Nat.le_succ N)) _))
    have he0 : Tendsto e atTop (𝓝 0) :=
      (gradientMeshError_tendsto_zero hT hT1 h).comp (tendsto_add_atTop_nat 1)
    have hδ0 : Tendsto (fun N : ℕ ↦ stepSize T (N+1)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 1)
    have hrend0 : Tendsto rend atTop (𝓝 0) := by
      simpa only [rend, Function.comp_def, Real.sqrt_zero, zero_mul] using
        ((Real.continuous_sqrt.tendsto 0).comp hδ0).mul_const D
    have herr := shiftedPairing_tendsto_error_zero
      (fun N ↦ gradientMeshError_nonneg T (N+1) γ u) (mul_nonneg (Real.sqrt_nonneg T) hD0)
      (hproj.mono (fun _ hN ↦ hN.1)) (hproj.mono (fun _ hN ↦ hN.2))
      (Eventually.of_forall (fun N ↦ (hnorm N).1)) (Eventually.of_forall hαnorm)
      (Eventually.of_forall (fun N ↦ (hnorm N).2)) (Eventually.of_forall hend) he0 hrend0
    let v (N : ℕ) (i : Fin N) :=
      (∫ z, meshRaw T (N+1) γ u (i+1) z ∂gaussianProduct (Fin ((N+1)+1)))*Real.sqrt (q (N+1) i)
    have hv (N : ℕ) (i : Fin N) :
        |v N i-f ((i+1 : ℕ)*(T/(N+1)))|≤(D+1)*r (N+1) := by
      apply product_perturbation_bound hD0 (hr (N+1))
      · exact mesh_mean_bound hT.le hD (Nat.succ_pos N) (by omega)
      · exact (abs_sqrt_sub_one_le (integral_nonneg (fun z ↦ sq_nonneg _))).trans
          (hq (N+1) (Nat.succ_pos N) i.castSucc)
      · simpa only [meshTime, stepSize, Fin.val_succ, Nat.cast_add, Nat.cast_one] using
          hm (N+1) (Nat.succ_pos N) i.succ
    have hv0 : Tendsto (fun N ↦ (D+1)*r (N+1)) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using (hr0.comp (tendsto_add_atTop_nat 1)).const_mul (D+1)
    have hvlim := perturbed_shifted_grid_tendsto hT hf
      (fun N ↦ mul_nonneg (by positivity : 0≤D+1) (hr (N+1))) hv0 (Eventually.of_forall hv)
    have hsum (N : ℕ) : (∑ i : Fin N, α N i.castSucc*β N i.succ)=
        (T/(N+1))*∑ i : Fin N, v N i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hδ : 0 ≤ stepSize T (N+1) := div_nonneg hT.le (Nat.cast_nonneg _)
      dsimp only [α, β, v, q, predictableNormalizer]
      rw [div_inv_eq_mul]
      calc
        _ = (Real.sqrt (stepSize T (N+1)))^2 *
          ((∫ z, meshRaw T (N+1) γ u (i+1) z ∂gaussianProduct (Fin ((N+1)+1)))*
            Real.sqrt (∫ z, (meshRaw T (N+1) γ u i z)^2 ∂gaussianProduct (Fin ((N+1)+1)))) := by
              simp only [Fin.val_castSucc, Fin.val_succ]
              ring
        _ = _ := by rw [Real.sq_sqrt hδ]; simp only [stepSize, Nat.cast_add, Nat.cast_one]
    have hp (N : ℕ) : shiftedPairing (A N) (B N) (bstar N)=finiteShiftedValue T (N+1) γ u := by
      simp only [shiftedPairing, finiteShiftedValue, A, B, bstar]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]
    simp_rw [hp, hsum] at herr
    have hlim := herr.add hvlim
    simp only [sub_add_cancel, zero_add] at hlim
    exact (tendsto_add_atTop_iff_nat 1).mp hlim

end SKValue

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators

end

end OAI
