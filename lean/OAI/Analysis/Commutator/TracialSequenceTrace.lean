import Mathlib
import OAI.Analysis.Commutator.TracialSequenceRight

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison

namespace VectorFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def functional (x : H) : (H →L[ℂ] H) →ₚ[ℂ] ℂ where
  toLinearMap := {
    toFun T := inner ℂ x (T x)
    map_add' := by intro S T; simp only [add_apply,inner_add_right]
    map_smul' := by intro c T; simp only [smul_apply,inner_smul_right,smul_eq_mul,RingHom.id_apply] }
  monotone' := by
    intro S T hST
    apply sub_nonneg.mp
    rw [←inner_sub_right,←sub_apply]
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hST)).inner_nonneg_right x

omit [CompleteSpace H] in
@[simp] lemma functional_apply (x : H) (T : H →L[ℂ] H) :
    functional x T=inner ℂ x (T x) := rfl

lemma functional_star_mul (x : H) (T : H →L[ℂ] H) :
    functional x (star T*T)=inner ℂ (T x) (T x) := by
  rw [functional_apply,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

omit [CompleteSpace H] in
lemma continuous_functional_wot (x : H) :
    Continuous (fun T : H →WOT[ℂ] H => inner ℂ x (T x)) :=
  ContinuousLinearMapWOT.continuous_dual_apply x (innerSL ℂ x)

end VectorFunctional

namespace TracialSequence

open TracialGNS HilbertSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

def sequenceTrace : (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) →ₚ[ℂ] ℂ :=
  VectorFunctional.functional (sequenceVacuum τ ω)

lemma tendsto_trace (a : ℕ →ᵇ A) : Tendsto (fun i => τ (a i)) (ω : Filter ℕ)
    (𝓝 (sequenceTrace τ ω (leftRestricted τ ω a))) := by
  change Tendsto _ _ (𝓝 (inner ℂ (sequenceVacuum τ ω) (leftRestricted τ ω a (sequenceVacuum τ ω))))
  rw [leftRestricted_vacuum]
  change Tendsto _ _ (𝓝 (inner ℂ (vector τ ω 1) (vector τ ω a)))
  change Tendsto _ _ (𝓝 (inner ℂ (vectorPre τ ω 1 : Space ω τ.GNS) (vectorPre τ ω a : Space ω τ.GNS)))
  rw [Completion.inner_coe]
  simpa only [vectorPre_seq,BoundedContinuousFunction.coe_one,Pi.one_apply,inner_algebraVector,star_one,one_mul] using
    tendsto_inner ω τ.GNS (vectorPre τ ω 1) (vectorPre τ ω a)

lemma trace_one : sequenceTrace τ ω 1=τ 1 := by
  have h := tendsto_trace τ ω (1 : ℕ →ᵇ A)
  simp only [map_one] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
lemma trace_mul (a b : ℕ →ᵇ A) : sequenceTrace τ ω (leftRestricted τ ω (a*b))=
    sequenceTrace τ ω (leftRestricted τ ω (b*a)) := by
  apply tendsto_nhds_unique (tendsto_trace τ ω (a*b))
  simpa only [BoundedContinuousFunction.mul_apply,hτ] using tendsto_trace τ ω (b*a)

include hτ in
lemma trace_faithful {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hz : sequenceTrace τ ω (star T*T)=0) : T=0 := by
  have hv : T (sequenceVacuum τ ω)=0 := by
    rw [sequenceTrace,VectorFunctional.functional_star_mul] at hz
    exact inner_self_eq_zero.mp hz
  apply bicommutant_eq_of_vacuum τ ω hτ T 0 hT
  · intro b _; simp
  · simpa only [zero_apply] using hv

end TracialSequence

end Kadison

end

end
end

end OAI
