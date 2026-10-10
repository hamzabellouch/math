import Mathlib

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X]

lemma continuous_variable_eval : Continuous (fun p : (X → X) × X => p.1 p.2) :=
  continuous_prod_of_discrete_right.mpr fun x => continuous_apply x

variable (Γ : SimpleGraph X)

def coordinates (g : Γ ≃g Γ) : (X → X) × (X → X) := (g,g.symm)

@[instance_reducible] def autTopology : TopologicalSpace (Γ ≃g Γ) :=
  TopologicalSpace.induced (coordinates Γ) inferInstance

local instance : TopologicalSpace (Γ ≃g Γ) := autTopology Γ

omit [DiscreteTopology X] in
lemma coordinates_embedding : IsEmbedding (coordinates Γ) where
  eq_induced := rfl
  injective := by
    intro g h he
    apply RelIso.ext
    intro x
    exact congrFun (congrArg Prod.fst he) x

omit [DiscreteTopology X] in
lemma continuous_eval (x : X) : Continuous (fun g : Γ ≃g Γ => g x) :=
  (continuous_apply x).comp (continuous_fst.comp (coordinates_embedding Γ).continuous)

omit [DiscreteTopology X] in
lemma continuous_inv_eval (x : X) : Continuous (fun g : Γ ≃g Γ => g.symm x) :=
  (continuous_apply x).comp (continuous_snd.comp (coordinates_embedding Γ).continuous)

omit [TopologicalSpace X] [DiscreteTopology X] in
lemma coordinates_range : Set.range (coordinates Γ) =
    {p : (X → X) × (X → X) |
      (∀ x, p.2 (p.1 x)=x) ∧ (∀ x, p.1 (p.2 x)=x) ∧
      (∀ x y, Γ.Adj (p.1 x) (p.1 y) ↔ Γ.Adj x y)} := by
  ext p
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g.symm_apply_apply,g.apply_symm_apply,fun _ _ => g.map_adj_iff⟩
  · rintro ⟨hleft,hright,hadj⟩
    refine ⟨{toEquiv := ⟨p.1,p.2,hleft,hright⟩,map_rel_iff' := fun {x y} => hadj x y},?_⟩
    exact Prod.eta p

lemma coordinates_closed : IsClosed (Set.range (coordinates Γ)) := by
  rw [coordinates_range]
  simp only [Set.ofPred_and,Set.ofPred_forall]
  refine (isClosed_iInter fun x => ?_).inter ((isClosed_iInter fun x => ?_).inter
    (isClosed_iInter fun x => isClosed_iInter fun y => ?_))
  · change IsClosed {p : (X → X) × (X → X) | p.2 (p.1 x)=x}
    exact isClosed_eq ((continuous_variable_eval (X := X)).comp (continuous_snd.prodMk
      ((continuous_apply x).comp continuous_fst))) continuous_const
  · change IsClosed {p : (X → X) × (X → X) | p.1 (p.2 x)=x}
    exact isClosed_eq ((continuous_variable_eval (X := X)).comp (continuous_fst.prodMk
      ((continuous_apply x).comp continuous_snd))) continuous_const
  · change IsClosed {p : (X → X) × (X → X) | Γ.Adj (p.1 x) (p.1 y) ↔ Γ.Adj x y}
    exact (isClosed_discrete {p : X × X | Γ.Adj p.1 p.2 ↔ Γ.Adj x y}).preimage
      (show Continuous (fun p : (X → X) × (X → X) => (p.1 x,p.1 y)) from
        ((continuous_apply x).comp continuous_fst).prodMk
          ((continuous_apply y).comp continuous_fst))

lemma coordinates_closedEmbedding : IsClosedEmbedding (coordinates Γ) :=
  ⟨coordinates_embedding Γ,coordinates_closed Γ⟩

instance aut_t2 : T2Space (Γ ≃g Γ) := (coordinates_embedding Γ).t2Space

instance aut_topologicalGroup : IsTopologicalGroup (Γ ≃g Γ) where
  continuous_mul := by
    apply (coordinates_embedding Γ).continuous_iff.mpr
    apply Continuous.prodMk
    · apply continuous_pi
      intro x
      exact continuous_variable_eval.comp
        (((continuous_fst.comp (coordinates_embedding Γ).continuous).comp continuous_fst).prodMk
          ((continuous_eval Γ x).comp continuous_snd))
    · apply continuous_pi
      intro x
      exact continuous_variable_eval.comp
        (((continuous_snd.comp (coordinates_embedding Γ).continuous).comp continuous_snd).prodMk
          ((continuous_inv_eval Γ x).comp continuous_fst))
  continuous_inv := by
    apply (coordinates_embedding Γ).continuous_iff.mpr
    exact (continuous_snd.comp (coordinates_embedding Γ).continuous).prodMk
      (continuous_fst.comp (coordinates_embedding Γ).continuous)

lemma compact_coordinate_bounds (F : X → Set X) (hF : ∀ x, (F x).Finite) :
    IsCompact {g : Γ ≃g Γ | (∀ x, g x∈F x) ∧ (∀ x, g.symm x∈F x)} := by
  have hK : IsCompact {f : X → X | ∀ x, f x∈F x} :=
    isCompact_pi_infinite fun x => (hF x).isCompact
  exact (coordinates_closedEmbedding Γ).isCompact_preimage (hK.prod hK)

lemma isClosed_eval_mem (x : X) (S : Set X) :
    IsClosed {g : Γ ≃g Γ | g x∈S} :=
  (isClosed_discrete S).preimage (continuous_eval Γ x)

lemma isOpen_eval_mem (x : X) (S : Set X) :
    IsOpen {g : Γ ≃g Γ | g x∈S} :=
  (isOpen_discrete S).preimage (continuous_eval Γ x)

end CriticalPercolation.GraphTopology
end
end

end OAI
