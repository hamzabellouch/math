import Mathlib
import OAI.Analysis.FreeWords.TraceTransferDefinitions

namespace OAI

noncomputable section

open scoped ComplexConjugate InnerProductSpace BoundedContinuousFunction

namespace UniversalStrongKK

section OperatorMean

variable {G H : Type*} [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (m : ScalarMean G)

variable [CompleteSpace H]

end OperatorMean

end UniversalStrongKK

open scoped Topology

namespace UniversalStrongKK

section UltraMean

variable {I : Type*} [TopologicalSpace I]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end UltraMean

end UniversalStrongKK

namespace UniversalStrongKK

open scoped InnerProductSpace

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end UniversalStrongKK

namespace KKTraceTransfer

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

end KKTraceTransfer

namespace KKTraceTransfer

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma trace_square_nonneg {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (x : ConcreteAlgebra M) : 0 ≤ τ.map (star x * x) := by
  apply τ.positive
  exact ContinuousLinearMap.isPositive_adjoint_comp_self (x : H →L[ℂ] H)

lemma traceNorm_sq {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (x : ConcreteAlgebra M) : (((traceNorm τ x)^2 : ℝ) : ℂ) = τ.map (star x * x) := by
  have hp := Complex.nonneg_iff.mp (trace_square_nonneg τ x)
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    simpa [traceNorm] using Real.sq_sqrt hp.1
  · simpa only [Complex.ofReal_im] using hp.2

lemma trace_square_tendsto {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (ω : Ultrafilter ℕ) (x : ℕ → ConcreteAlgebra M)
    (hnull : Tendsto (fun j => traceNorm τ (x j)) (ω : Filter ℕ) (𝓝 0)) :
    Tendsto (fun j => τ.map (star (x j) * x j)) (ω : Filter ℕ) (𝓝 0) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (hnull.pow 2)
  simp only [zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero] at h
  convert h using 1
  funext j
  exact (traceNorm_sq τ (x j)).symm

theorem trace_transfer {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (ω : Ultrafilter ℕ) (x : ℕ → ConcreteAlgebra M)
    (hbound : ∃ C : ℝ, ∀ j, ‖x j‖ ≤ C)
    (hnull : Tendsto (fun j => traceNorm τ (x j)) (ω : Filter ℕ) (𝓝 0)) (ξ : H) :
    Tendsto (fun j => ‖(x j : H →L[ℂ] H) ξ‖) (ω : Filter ℕ) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hbound
  have hC0 : 0 ≤ C := (norm_nonneg (x 0)).trans (hC 0)
  have hTb (j : ℕ) : ‖(star (x j) * x j : ConcreteAlgebra M)‖ ≤ C^2 := by
    change ‖star (x j : H →L[ℂ] H) * (x j : H →L[ℂ] H)‖ ≤ C^2
    rw [CStarRing.norm_star_mul_self, ← sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC j) 2
  let T : ℕ →ᵇ (H →L[ℂ] H) := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun j => (star (x j) * x j : ConcreteAlgebra M)) continuous_of_discreteTopology
    (C^2) hTb
  let A := UniversalStrongKK.operatorMean (UniversalStrongKK.ultrafilterMean ω) T
  have ht := UniversalStrongKK.tendsto_operatorMean ω T
  have hm (j : ℕ) : T j ∈ M := (star (x j) * x j : ConcreteAlgebra M).property
  have hA : A ∈ M := UniversalStrongKK.mem_of_wot_tendsto M ht
    (Filter.Eventually.of_forall hm)
  have hAp : A.IsPositive := UniversalStrongKK.positive_of_wot_tendsto ht
    (Filter.Eventually.of_forall fun j =>
      ContinuousLinearMap.isPositive_adjoint_comp_self (x j : H →L[ℂ] H))
  have hAb : ‖A‖ ≤ C^2 := UniversalStrongKK.norm_le_of_wot_tendsto (sq_nonneg C) ht
    (Filter.Eventually.of_forall hTb)
  let Aw : WeakAlgebra M := ⟨ContinuousLinearMapWOT.ofCLM A, hA⟩
  let Tw : ℕ → WeakAlgebra M := fun j => ⟨ContinuousLinearMapWOT.ofCLM (T j), hm j⟩
  have ht' : Tendsto Tw (ω : Filter ℕ) (𝓝 Aw) := tendsto_subtype_rng.mpr ht
  have ht'' : Tendsto Tw (ω : Filter ℕ) (𝓝[{T : WeakAlgebra M | ‖T.val.toCLM‖ ≤ C^2}] Aw) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht', Filter.Eventually.of_forall hTb⟩
  have hτA := (τ.normal (C^2) Aw hAb).tendsto.comp ht''
  have hτ0 := trace_square_tendsto τ ω x hnull
  have hz : τ.map (weakToAlgebra Aw) = 0 := tendsto_nhds_unique hτA hτ0
  have hAz : A = 0 := congrArg Subtype.val (τ.faithful (weakToAlgebra Aw) hAp hz)
  have hv := (Complex.continuous_re.continuousAt.tendsto.comp
    (ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp ht ξ ξ))
  change Tendsto (fun j => (⟪ξ, (star (x j : H →L[ℂ] H) *
    (x j : H →L[ℂ] H)) ξ⟫_ℂ).re) (ω : Filter ℕ) (𝓝 ((⟪ξ, A ξ⟫_ℂ).re)) at hv
  have hnormsq : Tendsto (fun j => ‖(x j : H →L[ℂ] H) ξ‖^2) (ω : Filter ℕ) (𝓝 0) := by
    simp only [hAz, zero_apply, inner_zero_right, Complex.zero_re, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right] at hv
    change Tendsto (fun j => RCLike.re ⟪(x j : H →L[ℂ] H) ξ, (x j : H →L[ℂ] H) ξ⟫_ℂ)
      (ω : Filter ℕ) (𝓝 0) at hv
    simpa only [inner_self_eq_norm_sq] using hv
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hnormsq
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hs

end

end KKTraceTransfer
end

end OAI
