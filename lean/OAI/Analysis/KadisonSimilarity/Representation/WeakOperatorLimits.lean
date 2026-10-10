import OAI.Analysis.KadisonSimilarity.Representation.Amplification
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

namespace OAI

/-! The norm estimates and commutation identities used in symmetrization
persist under weak-operator limits. -/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMapWOT
open scoped Topology

variable {H K ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A homogeneous bound on all Hilbert matrix coefficients bounds the
operator norm with the same constant. -/
theorem norm_le_of_matrix_coefficients (T : H →L[ℂ] K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x y, ‖inner ℂ y (T x)‖ ≤ c * ‖y‖ * ‖x‖) : ‖T‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have hx := h x (T x)
  rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq] at hx
  by_cases hz : ‖T x‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖T x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

variable [CompleteSpace K]

/-- Bounded closed balls are weak-operator closed, in the sequential or
general-filter form needed by the averaging argument. -/
theorem norm_le_of_weakOperator_tendsto {l : Filter ι} [l.NeBot]
    (T : ι → H →L[ℂ] K) (S : H →L[ℂ] K)
    (ht : Tendsto (fun i => ofCLM (T i)) l (𝓝 (ofCLM S)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ i in l, ‖T i‖ ≤ c) : ‖S‖ ≤ c := by
  apply norm_le_of_matrix_coefficients S hc
  intro x y
  have hlim := (tendsto_iff_forall_inner_apply_tendsto.mp ht x y).norm
  apply le_of_tendsto hlim
  filter_upwards [hbound] with i hi
  calc
    ‖inner ℂ y (T i x)‖ ≤ ‖y‖ * ‖T i x‖ := norm_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖T i‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((T i).le_opNorm x) (norm_nonneg y)
    _ ≤ ‖y‖ * (c * ‖x‖) := by gcongr
    _ = c * ‖y‖ * ‖x‖ := by ring

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- Commutation against a fixed bounded operator is weak-operator continuous. -/
theorem weakOperator_tendsto_commutator {l : Filter ι}
    (T : ι → H →L[ℂ] H) (S A : H →L[ℂ] H)
    (ht : Tendsto (fun i => ofCLM (T i)) l (𝓝 (ofCLM S))) :
    Tendsto (fun i => ofCLM (commutator (T i) A)) l
      (𝓝 (ofCLM (commutator S A))) := by
  change Tendsto (fun i => ofCLM (T i) * ofCLM A - ofCLM A * ofCLM (T i)) l
    (𝓝 (ofCLM S * ofCLM A - ofCLM A * ofCLM S))
  exact (ht.mul_const _).sub (ht.const_mul _)

/-- A fixed commutator estimate survives weak-operator convergence. -/
theorem norm_commutator_le_of_weakOperator_tendsto {l : Filter ι} [l.NeBot]
    (T : ι → H →L[ℂ] H) (S A : H →L[ℂ] H)
    (ht : Tendsto (fun i => ofCLM (T i)) l (𝓝 (ofCLM S)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ i in l, ‖commutator (T i) A‖ ≤ c) :
    ‖commutator S A‖ ≤ c :=
  norm_le_of_weakOperator_tendsto _ _ (weakOperator_tendsto_commutator T S A ht) hc hbound

/-- In particular exact commutation survives these limits. -/
theorem commutator_eq_zero_of_weakOperator_tendsto {l : Filter ι} [l.NeBot]
    (T : ι → H →L[ℂ] H) (S A : H →L[ℂ] H)
    (ht : Tendsto (fun i => ofCLM (T i)) l (𝓝 (ofCLM S)))
    (hcomm : ∀ᶠ i in l, commutator (T i) A = 0) : commutator S A = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply norm_commutator_le_of_weakOperator_tendsto T S A ht (le_refl 0)
  filter_upwards [hcomm] with i hi
  simp only [hi, norm_zero, le_refl]

/-- The entire scalar commutator seminorm is lower semicontinuous for the
weak-operator topology. -/
theorem scalarCommutatorNorm_le_of_weakOperator_tendsto {l : Filter ι} [l.NeBot]
    (P : VonNeumannAlgebra H) (T : ι → H →L[ℂ] H) (S : H →L[ℂ] H)
    (ht : Tendsto (fun i => ofCLM (T i)) l (𝓝 (ofCLM S)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ i in l, scalarCommutatorNorm P (T i) ≤ c) :
    scalarCommutatorNorm P S ≤ c := by
  apply (scalarCommutatorNorm_le_iff P S hc).2
  intro A hA
  apply norm_commutator_le_of_weakOperator_tendsto T S A ht (by positivity)
  filter_upwards [hbound] with i hi
  exact (norm_commutator_le_scalarCommutatorNorm P (T i) A hA).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg A))

end KadisonSimilarity

end

end OAI
