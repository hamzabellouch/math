import OAI.Analysis.BoundedHochschild.WeakRightAveraging
import OAI.Analysis.BoundedHochschild.CompactInvariantSets

namespace OAI

/-! The compact invariant family of elementary right averages. This is the
compactness portion of the module projection construction; it does not yet
assert that a member of the family is a right module map. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

/-- All finite normalized elementary right averages of one map. -/
def rightAverageOrbit (T : M →L[ℂ] M) : Set (M →L[ℂ] M) :=
  {S | ∃ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) ∧
    S = finiteRightAverage m T}

lemma finiteRightAverage_mem_orbit {I : Type*} [Fintype I]
    (m : I → M) (hm : ∑ i, m i * star (m i) = 1) (T : M →L[ℂ] M) :
    finiteRightAverage m T ∈ rightAverageOrbit T := by
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, m ∘ e.symm, ?_, ?_⟩
  · exact (e.symm.sum_comp (fun i => m i * star (m i))).trans hm
  · exact (finiteRightAverage_reindex e.symm m T).symm

lemma self_mem_rightAverageOrbit (T : M →L[ℂ] M) : T ∈ rightAverageOrbit T := by
  have h := finiteRightAverage_mem_orbit (fun _ : Fin 1 => (1 : M)) (by simp) T
  have heq : finiteRightAverage (fun _ : Fin 1 => (1 : M)) T = T := by
    ext a
    simp only [finiteRightAverage_apply, mul_one, star_one, Fin.sum_univ_one]
  rwa [heq] at h

lemma rightAverageOrbit_invariant {I : Type*} [Fintype I]
    (m : I → M) (hm : ∑ i, m i * star (m i) = 1) (T : M →L[ℂ] M) :
    Set.MapsTo (finiteRightAverage m) (rightAverageOrbit T) (rightAverageOrbit T) := by
  rintro S ⟨n, v, hv, rfl⟩
  rw [finiteRightAverage_comp]
  exact finiteRightAverage_mem_orbit _ (rightAverage_product_normalized m v hm hv) T

lemma rightAverageOrbit_convex (T : M →L[ℂ] M) : Convex ℝ (rightAverageOrbit T) := by
  rintro S ⟨n, m, hm, rfl⟩ U ⟨k, v, hv, rfl⟩ r s hr hs hrs
  rw [← finiteRightAverage_convex m v hr hs T]
  exact finiteRightAverage_mem_orbit _ (rightAverage_convex_normalized m v hm hv hr hs hrs) T

universe u
variable {N X : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma rightAverageOrbit_norm_le (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
    (hno : NoFiniteCentralSummand N) (T : N →L[ℂ] N) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) {S : N →L[ℂ] N}
    (hS : S ∈ rightAverageOrbit T) : ‖S‖ ≤ C := by
  obtain ⟨n, m, hm, rfl⟩ := hS
  cases n with
  | zero =>
      have heq : finiteRightAverage m T = 0 := by
        ext a
        simp only [finiteRightAverage_apply, Fin.sum_univ_zero, zero_apply]
      rw [heq, norm_zero]
      exact hT.1
  | succ n => exact finiteRightAverage_norm_of_completelyBounded e hno m hm T hT

/-- Pointwise weak-star closure of the finite averaging orbit. -/
def weakRightAverageOrbit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N) (T : N →L[ℂ] N) :
    Set (N → WeakDual ℂ X) := closure (weakOperatorImage e '' rightAverageOrbit T)

omit [PartialOrder N] [StarOrderedRing N] [CompleteSpace X] in
lemma weakRightAverageOrbit_nonempty (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
    (T : N →L[ℂ] N) : (weakRightAverageOrbit e T).Nonempty :=
  ⟨weakOperatorImage e T, subset_closure ⟨T, self_mem_rightAverageOrbit T, rfl⟩⟩

lemma weakRightAverageOrbit_subset_ball (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
    (hno : NoFiniteCentralSummand N) (T : N →L[ℂ] N) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) : weakRightAverageOrbit e T ⊆ weakOperatorBall C := by
  apply closure_minimal _ (weakOperatorBall_isClosed C)
  rintro F ⟨S, hS, rfl⟩
  exact weakOperatorImage_mem e S (rightAverageOrbit_norm_le e hno T hT hS)

theorem weakRightAverageOrbit_isCompact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
    (hno : NoFiniteCentralSummand N) (T : N →L[ℂ] N) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) : IsCompact (weakRightAverageOrbit e T) :=
  (weakOperatorBall_isCompact C).of_isClosed_subset isClosed_closure
    (weakRightAverageOrbit_subset_ball e hno T hT)

omit [PartialOrder N] [StarOrderedRing N] in
lemma weakRightAverageOrbit_invariant {I : Type*} [Fintype I]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N) (m : I → N) (hm : ∑ i, m i * star (m i) = 1)
    (T : N →L[ℂ] N) :
    Set.MapsTo (weakRightAverage e m) (weakRightAverageOrbit e T) (weakRightAverageOrbit e T) := by
  have h : Set.MapsTo (weakRightAverage e m) (weakOperatorImage e '' rightAverageOrbit T)
      (weakOperatorImage e '' rightAverageOrbit T) := by
    rintro F ⟨S, hS, rfl⟩
    rw [weakRightAverage_image]
    exact ⟨finiteRightAverage m S, rightAverageOrbit_invariant m hm T hS, rfl⟩
  exact h.closure (weakRightAverage_continuous e m)

omit [PartialOrder N] [StarOrderedRing N] [CompleteSpace X] in
lemma weakRightAverageOrbit_convex (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
    (T : N →L[ℂ] N) : Convex ℝ (weakRightAverageOrbit e T) := by
  have hc : Convex ℝ (weakOperatorImage e '' rightAverageOrbit T) :=
    (rightAverageOrbit_convex T).linear_image (weakOperatorImageLinear e)
  intro F hF G hG r s hr hs hrs
  have hcont : Continuous (fun p : (N → WeakDual ℂ X) × (N → WeakDual ℂ X) =>
      r • p.1 + s • p.2) := by
    apply continuous_pi
    intro a
    apply WeakDual.continuous_of_continuous_eval
    intro x
    change Continuous (fun p : (N → WeakDual ℂ X) × (N → WeakDual ℂ X) =>
      r • p.1 a x + s • p.2 a x)
    exact (((WeakDual.eval_continuous x).comp ((continuous_apply a).comp continuous_fst)).const_smul r).add
      (((WeakDual.eval_continuous x).comp ((continuous_apply a).comp continuous_snd)).const_smul s)
  exact map_mem_closure₂ (f := fun U V => r • U + s • V) hcont hF hG
    (fun _ hU _ hV => hc hU hV hr hs hrs)

end BoundedHochschild.KadisonRingrose

end

end OAI
