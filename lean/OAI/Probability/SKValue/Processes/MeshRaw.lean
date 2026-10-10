import Mathlib
import OAI.Probability.SKValue.Equations.FiniteRounded

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

noncomputable def meshRaw (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (j : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  deriv (u (meshTime T N j)) (euler T N γ u z j)

noncomputable def meshTerminal (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (z : Fin (N+1) → ℝ) : ℝ := u T (euler T N γ u z N)

noncomputable def meshA (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (j : ℕ) : ℝ :=
  ∫ z, finiteRounded (meshTerminal T N γ u) z *
    normalizedIncrement (meshRaw T N γ u j) (coordinate N j) (gaussianProduct (Fin (N+1))) z
    ∂gaussianProduct (Fin (N+1))

noncomputable def meshB (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (j : ℕ) : ℝ :=
  ∫ z, finiteRounded (meshTerminal T N γ u) z * coordinate N j z ∂gaussianProduct (Fin (N+1))

noncomputable def finiteShiftedValue (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : ℝ :=
  ∑ i : Fin N, meshA T N γ u i * meshB T N γ u (i+1)

lemma mesh_time_mem {T : ℝ} (hT : 0≤T) {N j : ℕ} (hN : 0<N) (hj : j≤N) :
    meshTime T N j∈Icc (0 : ℝ) T := by
  apply mesh_mem_strip_ito (δ := stepSize T N) (div_nonneg hT (Nat.cast_nonneg N)) _ hj
  have hNr : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold stepSize
  field_simp

lemma mesh_terminal_measurable {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    Measurable (meshTerminal T N γ u) :=
  (h.smooth T ⟨hT,le_rfl⟩).continuous.measurable.comp
    (measurable_euler T N γ u (fun _ hj ↦
      (h.smooth _ (mesh_time_mem hT hN hj.le)).continuous.measurable) N le_rfl)

lemma mesh_raw_measurable {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    Measurable (meshRaw T N γ u j) :=
  ((h.smooth _ (mesh_time_mem hT hN hj)).continuous_deriv (by norm_num)).measurable.comp
    (measurable_euler T N γ u (fun k hk ↦
      (h.smooth _ (mesh_time_mem hT hN hk.le)).continuous.measurable) j hj)

lemma mesh_raw_depends (T : ℝ) {N j : ℕ} (hj : j≤N) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) :
    DependsBefore j (meshRaw T N γ u j) :=
  eulerCoefficient_dependsBefore T hj γ u (fun t ↦ deriv (u t))

lemma mesh_terminal_depends (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) :
    DependsBefore N (meshTerminal T N γ u) :=
  eulerCoefficient_dependsBefore T le_rfl γ u (fun _ ↦ u T)

lemma mesh_raw_memLp {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    MemLp (meshRaw T N γ u j) 2 (gaussianProduct (Fin (N+1))) := by
  have := gaussianProduct_probability (Fin (N+1))
  apply MemLp.of_bound (mesh_raw_measurable hT h hN hj).aestronglyMeasurable D
  exact Eventually.of_forall (fun z ↦ by
    simpa only [meshRaw, Real.norm_eq_abs] using hD _ (mesh_time_mem hT hN hj) (euler T N γ u z j))

lemma mesh_coefficient_errors {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N)
    (hpos : ∀ j : Fin N, 0<∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1))) :
    (∑ j : Fin N, (meshA T N γ u j-Real.sqrt (stepSize T N)/
      predictableNormalizer (meshRaw T N γ u j) (gaussianProduct (Fin (N+1))))^2)≤
      gradientMeshError T N γ u ∧
    (∑ j : Fin N, (meshB T N γ u j-Real.sqrt (stepSize T N)*
      ∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1)))^2)≤
      gradientMeshError T N γ u := by
  exact finite_coefficient_L2_errors
    (fun j ↦ mesh_raw_measurable hT h hN j.isLt.le)
    (fun j ↦ mesh_raw_depends T j.isLt.le γ u)
    (fun j ↦ mesh_raw_memLp hT h hD hN j.isLt.le) hpos
    (mesh_terminal_measurable hT h hN) (mesh_terminal_depends T N γ u)
    (fun z ↦ h.bounded T ⟨hT,le_rfl⟩ _)

lemma mesh_coefficients_norms {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    (∑ j : Fin N, (meshB T N γ u j)^2)≤1 ∧ |meshB T N γ u N|≤1 :=
  finiteRounded_coordinate_norms (mesh_terminal_measurable hT h hN)

lemma mesh_leading_norm {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) (hD0 : 0≤D)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) :
    (∑ j : Fin N, (Real.sqrt (stepSize T N)/
      predictableNormalizer (meshRaw T N γ u j) (gaussianProduct (Fin (N+1))))^2)≤
      (Real.sqrt T*D)^2 := by
  have := gaussianProduct_probability (Fin (N+1))
  have hδ : 0 ≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  calc
    _ ≤ ∑ j : Fin N, (Real.sqrt (stepSize T N)*D)^2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [←sq_abs (Real.sqrt _ / _)]
      apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hD0)).2
      exact sqrt_div_normalizer_bound (mesh_raw_memLp hT h hD hN j.isLt.le) hD0
        (Eventually.of_forall (fun z ↦ hD _ (mesh_time_mem hT hN j.isLt.le) _))
    _ = (Real.sqrt T*D)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow]
      rw [Real.sq_sqrt hδ, Real.sq_sqrt hT]
      unfold stepSize
      have hNr : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
      field_simp

lemma abs_sqrt_sub_one_le {q : ℝ} (hq : 0≤q) : |Real.sqrt q-1|≤|q-1| := by
  have heq : |q-1|=|Real.sqrt q-1| * (Real.sqrt q+1) := by
    rw [←abs_of_nonneg (by positivity : 0≤Real.sqrt q+1), ←abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt hq]
  rw [heq]
  nlinarith [Real.sqrt_nonneg q, abs_nonneg (Real.sqrt q-1)]

end SKValue

end

end OAI
