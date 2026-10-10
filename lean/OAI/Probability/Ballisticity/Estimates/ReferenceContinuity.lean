import Mathlib
import OAI.Probability.Ballisticity.Estimates.LocalStoppedSplice

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.ReferenceClasses

section Closed
variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [DiscreteTopology H]

omit [AddCommGroup H] in
lemma finite_value_clopen (z : H) : IsClopen ({(z : OnePoint H)} : Set (OnePoint H)) := by
  refine ⟨isClosed_singleton,?_⟩
  simpa only [Set.image_singleton] using
    (OnePoint.isOpenMap_coe {z} (isOpen_discrete _))

omit [AddCommGroup H] in
lemma offset_clopen (a b : ℕ) (z : H) :
    IsClopen {O : Offsets H | O (a,b) = (z : OnePoint H)} :=
  (finite_value_clopen z).preimage (continuous_apply (a,b))

lemma consistent_closed : IsClosed {O : Offsets H | Consistent O} := by
  have hself : IsClosed {O : Offsets H | ∀ a, O (a,a) = ((0 : H) : OnePoint H)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => (offset_clopen a a 0).1
  have hsymm : IsClosed {O : Offsets H | ∀ (a b : ℕ) (z : H),
      O (a,b) = (z : OnePoint H) → O (b,a) = ((-z : H) : OnePoint H)} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun z => ?_
    have heq : {O : Offsets H | O (a,b) = (z : OnePoint H) → O (b,a) = ((-z : H) : OnePoint H)} =
        {O | O (a,b) = (z : OnePoint H)}ᶜ ∪ {O | O (b,a) = ((-z : H) : OnePoint H)} := by
      ext; simp [imp_iff_not_or]
    rw [heq]
    exact (offset_clopen a b z).2.isClosed_compl.union (offset_clopen b a (-z)).1
  have hadd : IsClosed {O : Offsets H | ∀ (a b c : ℕ) (z w : H),
      O (a,b) = (z : OnePoint H) → O (b,c) = (w : OnePoint H) →
      O (a,c) = ((z+w : H) : OnePoint H)} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun c =>
      isClosed_iInter fun z => isClosed_iInter fun w => ?_
    have heq : {O : Offsets H | O (a,b) = (z : OnePoint H) → O (b,c) = (w : OnePoint H) →
        O (a,c) = ((z+w : H) : OnePoint H)} =
      {O | O (a,b) = (z : OnePoint H)}ᶜ ∪
      ({O | O (b,c) = (w : OnePoint H)}ᶜ ∪ {O | O (a,c) = ((z+w : H) : OnePoint H)}) := by
      ext; simp [imp_iff_not_or]
    rw [heq]
    exact (offset_clopen a b z).2.isClosed_compl.union
      ((offset_clopen b c w).2.isClosed_compl.union (offset_clopen a c (z+w)).1)
  have heq : {O : Offsets H | Consistent O} =
      {O : Offsets H | ∀ a, O (a,a) = ((0 : H) : OnePoint H)} ∩
      {O : Offsets H | ∀ (a b : ℕ) (z : H),
        O (a,b) = (z : OnePoint H) → O (b,a) = ((-z : H) : OnePoint H)} ∩
      {O : Offsets H | ∀ (a b c : ℕ) (z w : H),
        O (a,b) = (z : OnePoint H) → O (b,c) = (w : OnePoint H) →
        O (a,c) = ((z+w : H) : OnePoint H)} := by
    ext O
    exact ⟨fun h => ⟨⟨h.self,h.symm⟩,h.add⟩,fun h => ⟨h.1.1,h.1.2,h.2⟩⟩
  rw [heq]
  exact (hself.inter hsymm).inter hadd

instance data_compact : CompactSpace (Data H) :=
  isCompact_iff_compactSpace.mp consistent_closed.isCompact

end Closed

section Reindex
variable {I J K R : Type*} [MeasurableSpace R]

lemma map_iid_eq_of_same_fibers (ν : Measure R) [IsProbabilityMeasure ν]
    (f : I → J) (g : I → K) (h : ∀ i i', f i = f i' ↔ g i = g i') :
    (Measure.infinitePi (fun _ : J => ν)).map (fun ξ i => ξ (f i)) =
      (Measure.infinitePi (fun _ : K => ν)).map (fun ξ i => ξ (g i)) := by
  classical
  let t : Set.range f → K := fun x => g (Classical.choose x.2)
  have ht (i : I) : t ⟨f i,Set.mem_range_self i⟩ = g i :=
    (h _ _).mp (Classical.choose_spec (Set.mem_range_self i))
  have htinj : Function.Injective t := by
    intro x y hxy
    apply Subtype.ext
    have hfg := (h (Classical.choose x.2) (Classical.choose y.2)).mpr hxy
    rw [Classical.choose_spec x.2,Classical.choose_spec y.2] at hfg
    exact hfg
  have h1 := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : J => ν)
    (f := (Subtype.val : Set.range f → J)) Subtype.val_injective
  have h2 := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : K => ν) htinj
  have hm : Measurable (fun ξ : Set.range f → R => fun i => ξ ⟨f i,Set.mem_range_self i⟩) := by
    fun_prop
  have hh := congrArg (fun μ : Measure (Set.range f → R) =>
    μ.map (fun ξ i => ξ ⟨f i,Set.mem_range_self i⟩)) (h1.trans h2.symm)
  rw [Measure.map_map hm (by fun_prop),Measure.map_map hm (by fun_prop)] at hh
  simpa only [Function.comp_def,ht] using hh

end Reindex

section FiniteCoordinates
variable {H R : Type*} [AddCommGroup H] [Countable H]
  [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)] [MeasurableSpace R]

lemma reference_projection_eq {I : Type*} (ν : Measure R) [IsProbabilityMeasure ν]
    (O O' : Data H) (p : I → Site H)
    (h : ∀ i j, inputSite O (p i) = inputSite O (p j) ↔
      inputSite O' (p i) = inputSite O' (p j)) :
    (reference ν O).map (fun φ i => φ (p i)) =
      (reference ν O').map (fun φ i => φ (p i)) := by
  have hm (D : Data H) : Measurable (fields D : AllFields H R → _) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  rw [reference_apply,reference_apply,Measure.map_map (by fun_prop) (hm O),
    Measure.map_map (by fun_prop) (hm O')]
  exact map_iid_eq_of_same_fibers ν (inputSite O ∘ p) (inputSite O' ∘ p) h

omit [Countable H] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)] in
lemma inputSite_collision_clopen (p q : Site H) :
    IsClopen {O : Data H | inputSite O p = inputSite O q} := by
  rcases p with ⟨a,l,z⟩
  rcases q with ⟨b,l',z'⟩
  simp only [inputSite_eq_iff]
  by_cases h : l = l'
  · simp only [h,true_and]
    exact (offset_clopen a b (z-z')).preimage continuous_subtype_val
  · simp only [h,false_and,Set.ofPred_false]
    exact isClopen_empty

lemma reference_projection_locally_constant {I : Type*} [Finite I]
    (ν : Measure R) [IsProbabilityMeasure ν] (O : Data H) (p : I → Site H) :
    ∀ᶠ O' in 𝓝 O, (reference ν O').map (fun φ i => φ (p i)) =
      (reference ν O).map (fun φ i => φ (p i)) := by
  have hh : ∀ᶠ O' in 𝓝 O, ∀ i j,
      inputSite O' (p i) = inputSite O' (p j) ↔ inputSite O (p i) = inputSite O (p j) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have hc := inputSite_collision_clopen (p i) (p j)
    by_cases h : inputSite O (p i) = inputSite O (p j)
    · filter_upwards [hc.2.mem_nhds h] with O' h'
      exact iff_of_true h' h
    · filter_upwards [hc.1.isOpen_compl.mem_nhds h] with O' h'
      exact iff_of_false h' h
  filter_upwards [hh] with O' h'
  exact reference_projection_eq ν O' O p h'

end FiniteCoordinates
end DirectionalTransience.ReferenceClasses

end

end OAI
