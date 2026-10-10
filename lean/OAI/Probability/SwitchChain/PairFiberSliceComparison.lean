import OAI.Probability.SwitchChain.PairFiberBridge
import OAI.Probability.SwitchChain.SlicePathComparison

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

open SlicePermutationAction
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def assignmentSliceEquiv (G : SimpleGraph V) (i j : V) :
    Assignment G i j ≃ Slice (singletonSet G i j) (leftSet G i j).card :=
  boundedSliceEquiv (singletonSet G i j) (leftSet G i j).card

def assignmentRelabel (G : SimpleGraph V) (i j : V)
    (σ : Equiv.Perm (singletonSet G i j)) (T : Assignment G i j) :
    Assignment G i j :=
  (assignmentSliceEquiv G i j).symm
    (relabel σ (assignmentSliceEquiv G i j T))

def assignmentRelabelEquiv (G : SimpleGraph V) (i j : V)
    (σ : Equiv.Perm (singletonSet G i j)) : Equiv.Perm (Assignment G i j) :=
  ((assignmentSliceEquiv G i j).trans (relabelEquiv σ)).trans
    (assignmentSliceEquiv G i j).symm

theorem assignmentRelabel_swap_val (G : SimpleGraph V) (i j : V)
    (x y : singletonSet G i j) (T : Assignment G i j) :
    (assignmentRelabel G i j (Equiv.swap x y) T).val =
      T.val.map (Equiv.swap x.val y.val).toEmbedding := by
  classical
  change ((T.val.subtype (fun z => z ∈ singletonSet G i j)).map
    (Equiv.swap x y).toEmbedding).map
      (Function.Embedding.subtype (fun z => z ∈ singletonSet G i j)) = _
  rw [Finset.map_map]
  have he : (Equiv.swap x y).toEmbedding.trans
      (Function.Embedding.subtype (fun z => z ∈ singletonSet G i j)) =
      (Function.Embedding.subtype (fun z => z ∈ singletonSet G i j)).trans
        (Equiv.swap x.val y.val).toEmbedding := by
    ext z
    exact Function.Injective.map_swap Subtype.val_injective x y z
  rw [he, ← Finset.map_map, Finset.subtype_map_of_mem T.property.1]

theorem assignment_variance_le_swap_energy (G : SimpleGraph V) (i j : V)
    (f : Assignment G i j → ℝ) :
    (∑ T, (f T - (∑ U, f U) / (Fintype.card (Assignment G i j) : ℝ)) ^ 2) ≤
      ((singletonSet G i j).card : ℝ) ^ 2 *
        ∑ T, f T * (∑ σ ∈ SlicePathComparison.swaps,
          (f T - f (assignmentRelabel G i j σ T))) := by
  classical
  let : Nonempty (Assignment G i j) :=
    ⟨⟨leftSet G i j, leftSet_subset_singletonSet G i j, rfl⟩⟩
  simpa only [Fintype.card_coe, assignmentRelabel] using
    SlicePathComparison.variance_le_card_sq_transport (assignmentSliceEquiv G i j) f

theorem assignment_displacement_eq_twice_energy (G : SimpleGraph V) (i j : V)
    (σ : Equiv.Perm (singletonSet G i j)) (f : Assignment G i j → ℝ) :
    (∑ T, (f T - f (assignmentRelabel G i j σ T)) ^ 2) =
      2 * (∑ T, f T * (f T - f (assignmentRelabel G i j σ T))) := by
  have hnorm : (∑ T, (f (assignmentRelabel G i j σ T)) ^ 2) = ∑ T, (f T)^2 :=
    Equiv.sum_comp (assignmentRelabelEquiv G i j σ) (fun T => (f T)^2)
  simp only [sub_sq, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum, ← sq]
  rw [hnorm]
  ring

theorem assignment_variance_le_swap_squared_differences (G : SimpleGraph V) (i j : V)
    (f : Assignment G i j → ℝ) :
    (∑ T, (f T - (∑ U, f U) / (Fintype.card (Assignment G i j) : ℝ)) ^ 2) ≤
      ((singletonSet G i j).card : ℝ) ^ 2 / 2 *
        ∑ T, ∑ σ ∈ SlicePathComparison.swaps,
          (f T - f (assignmentRelabel G i j σ T)) ^ 2 := by
  have h := assignment_variance_le_swap_energy G i j f
  have hs : (∑ T, ∑ σ ∈ SlicePathComparison.swaps,
      (f T - f (assignmentRelabel G i j σ T)) ^ 2) =
      2 * ∑ T, f T * (∑ σ ∈ SlicePathComparison.swaps,
        (f T - f (assignmentRelabel G i j σ T))) := by
    rw [Finset.sum_comm]
    simp_rw [assignment_displacement_eq_twice_energy]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro T _
    exact (Finset.mul_sum _ _ _).symm
  rw [hs]
  nlinarith [h]

def resamplingFiberSliceEquiv {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    (PairResampling.fiberStates {i, j} G) ≃
      Slice (singletonSet G.val i j) (leftSet G.val i j).card :=
  (resamplingFiberEquiv G i j hij).trans (assignmentSliceEquiv G.val i j)

theorem state_assignment_variance_le_swap_energy {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : GraphState n d → ℝ) :
    (∑ T : Assignment G.val i j,
      (f ((stateFiberEquiv G i j hij).symm T).val -
        (∑ U : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm U).val) /
          (Fintype.card (Assignment G.val i j) : ℝ)) ^ 2) ≤
      ((singletonSet G.val i j).card : ℝ) ^ 2 *
        ∑ T : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm T).val *
          (∑ σ ∈ SlicePathComparison.swaps,
            (f ((stateFiberEquiv G i j hij).symm T).val -
              f ((stateFiberEquiv G i j hij).symm (assignmentRelabel G.val i j σ T)).val)) :=
  assignment_variance_le_swap_energy G.val i j
    (fun T => f ((stateFiberEquiv G i j hij).symm T).val)

end Problem315.PairFiber

end

end OAI
