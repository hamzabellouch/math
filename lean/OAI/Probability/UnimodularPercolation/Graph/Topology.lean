import Mathlib

namespace OAI

/-! Pointwise topology on permutation groups. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
namespace PointwisePerm
open Topology Set
universe u
variable {X : Type u} [TopologicalSpace X] [DiscreteTopology X]

 
def coordinates (g : Equiv.Perm X) : (X → X) × (X → X) := (g, g.symm)

instance topology : TopologicalSpace (Equiv.Perm X) :=
  TopologicalSpace.induced coordinates inferInstance

omit [DiscreteTopology X] in
theorem isEmbedding_coordinates : Topology.IsEmbedding (coordinates (X := X)) := by
  refine ⟨⟨rfl⟩, ?_⟩
  intro g h he
  exact Equiv.ext (congrFun (congrArg Prod.fst he))

omit [DiscreteTopology X] in
theorem continuous_apply (x : X) : Continuous (fun g : Equiv.Perm X => g x) :=
  (_root_.continuous_apply x).comp (continuous_fst.comp isEmbedding_coordinates.continuous)

omit [DiscreteTopology X] in
theorem continuous_symm_apply (x : X) : Continuous (fun g : Equiv.Perm X => g.symm x) :=
  (_root_.continuous_apply x).comp (continuous_snd.comp isEmbedding_coordinates.continuous)

theorem continuous_eval : Continuous (fun p : (X → X) × X => p.1 p.2) :=
  continuous_prod_of_discrete_right.mpr fun x => _root_.continuous_apply x

instance topologicalGroup : IsTopologicalGroup (Equiv.Perm X) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · apply continuous_pi
      intro x
      exact (continuous_eval (X := X)).comp
        ((continuous_fst.comp (isEmbedding_coordinates.continuous.comp continuous_fst)).prodMk
          ((continuous_apply x).comp continuous_snd))
    · apply continuous_pi
      intro x
      exact (continuous_eval (X := X)).comp
        ((continuous_snd.comp (isEmbedding_coordinates.continuous.comp continuous_snd)).prodMk
          ((continuous_symm_apply x).comp continuous_fst))
  continuous_inv := by
    apply continuous_induced_rng.mpr
    exact (continuous_snd.comp isEmbedding_coordinates.continuous).prodMk
      (continuous_fst.comp isEmbedding_coordinates.continuous)

instance hausdorff : T2Space (Equiv.Perm X) :=
  isEmbedding_coordinates.t2Space

instance secondCountable [Countable X] : SecondCountableTopology (Equiv.Perm X) :=
  isEmbedding_coordinates.secondCountableTopology

 

theorem topology_eq_pointwise : topology (X := X) =
    TopologicalSpace.induced (fun g : Equiv.Perm X => (g : X → X)) inferInstance := by
  apply le_antisymm
  · exact continuous_iff_le_induced.mp
      (continuous_fst.comp isEmbedding_coordinates.continuous)
  · let t : TopologicalSpace (Equiv.Perm X) :=
      TopologicalSpace.induced (fun g : Equiv.Perm X => (g : X → X)) inferInstance
    have hc : @Continuous (Equiv.Perm X) ((X → X) × (X → X)) t _ coordinates := by
      let := t
      have hf : Continuous (fun g : Equiv.Perm X => (g : X → X)) := continuous_induced_dom
      have hi : Continuous (fun g : Equiv.Perm X => (g.symm : X → X)) := by
        apply continuous_pi
        intro x
        apply continuous_discrete_rng.mpr
        intro y
        have he : (fun g : Equiv.Perm X => g.symm x) ⁻¹' {y} =
            (fun g : Equiv.Perm X => g y) ⁻¹' {x} := by
          ext g
          simp only [Set.mem_preimage,Set.mem_singleton_iff]
          exact (Equiv.symm_apply_eq g).trans eq_comm
        rw [he]
        exact (isOpen_discrete _).preimage ((_root_.continuous_apply y).comp hf)
      exact hf.prodMk hi
    exact continuous_iff_le_induced.mp hc

 
omit [TopologicalSpace X] [DiscreteTopology X] in
theorem range_coordinates : Set.range (coordinates (X := X)) =
    {p | (∀ x, p.1 (p.2 x) = x) ∧ (∀ x, p.2 (p.1 x) = x)} := by
  ext p
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g.apply_symm_apply, g.symm_apply_apply⟩
  · rintro ⟨hfg,hgf⟩
    exact ⟨⟨p.1,p.2,hgf,hfg⟩,rfl⟩

theorem isClosed_range_coordinates : IsClosed (Set.range (coordinates (X := X))) := by
  rw [range_coordinates]
  have hf (x : X) : IsClosed {p : (X → X) × (X → X) | p.1 (p.2 x) = x} :=
    isClosed_eq
      ((continuous_eval (X := X)).comp (continuous_fst.prodMk ((_root_.continuous_apply x).comp continuous_snd)))
      continuous_const
  have hg (x : X) : IsClosed {p : (X → X) × (X → X) | p.2 (p.1 x) = x} :=
    isClosed_eq
      ((continuous_eval (X := X)).comp (continuous_snd.prodMk ((_root_.continuous_apply x).comp continuous_fst)))
      continuous_const
  convert (isClosed_iInter hf).inter (isClosed_iInter hg) using 1
  ext p
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

 

theorem isCompact_of_finite_images (S : Set (Equiv.Perm X)) (hS : IsClosed S)
    (hf : ∀ x, ((fun g : Equiv.Perm X => g x) '' S).Finite)
    (hg : ∀ x, ((fun g : Equiv.Perm X => g.symm x) '' S).Finite) :
    IsCompact S := by
  have he : Topology.IsClosedEmbedding (coordinates (X := X)) :=
    ⟨isEmbedding_coordinates, isClosed_range_coordinates⟩
  apply he.isEmbedding.isCompact_iff.mpr
  apply ((isCompact_pi_infinite fun x => (hf x).isCompact).prod
    (isCompact_pi_infinite fun x => (hg x).isCompact)).of_isClosed_subset
      (he.isClosedMap S hS)
  rintro _ ⟨g,hgS,rfl⟩
  exact ⟨fun x => ⟨g,hgS,rfl⟩, fun x => ⟨g,hgS,rfl⟩⟩

theorem isOpen_fixed (x y : X) : IsOpen {g : Equiv.Perm X | g x = y} :=
  (isOpen_discrete ({y} : Set X)).preimage (continuous_apply x)

theorem isClosed_fixed (x y : X) : IsClosed {g : Equiv.Perm X | g x = y} :=
  isClosed_eq (continuous_apply x) continuous_const

end PointwisePerm
end Percolation

end OAI
