import Mathlib
import OAI.Probability.Ballisticity.Estimates.Dust

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma measurable_countable_selection {X I : Type*} [MeasurableSpace X]
    [MeasurableSpace I] [Countable I] [Nonempty I]
    (P : X → I → Prop) (hP : ∀ i, MeasurableSet {x | P x i}) :
    ∃ s : X → I, Measurable s ∧ ∀ x, (∃ i, P x i) → P x (s x) := by
  let : Encodable I := Encodable.ofCountable I
  let z : I := Classical.choice ‹Nonempty I›
  let enum : ℕ → I := fun n => (Encodable.decode (α := I) n).getD z
  have he : ∀ i : I, enum (Encodable.encode i)=i := by
    intro i
    simp only [enum,Encodable.encodek,Option.getD_some]
  let Q : X → ℕ → Prop := fun x n => P x (enum n) ∨ ¬∃ i, P x i
  have hQ : ∀ x, ∃ n, Q x n := by
    intro x
    by_cases h : ∃ i, P x i
    · obtain ⟨i,hi⟩ := h
      exact ⟨Encodable.encode i,Or.inl (by simpa only [he] using hi)⟩
    · exact ⟨0,Or.inr h⟩
  have hQm (n : ℕ) : MeasurableSet {x | Q x n} := by
    exact (hP (enum n)).union (by
      have hm : MeasurableSet {x | ∃ i, P x i} := by
        simpa only [Set.ofPred_exists] using MeasurableSet.iUnion hP
      exact hm.compl)
  refine ⟨fun x => enum (Nat.find (hQ x)), (measurable_of_countable enum).comp (measurable_find hQ hQm),?_⟩
  intro x hx
  exact (Nat.find_spec (hQ x)).resolve_right (not_not.mpr hx)

def CurrentClassSelection {d : ℕ} (e : Direction d) (n : ℕ) (r : ℝ)
    (A : CurrentData e) (a : Fin n → ℕ) : Prop :=
  (∀ j, r≤(A.2 (a j,0):ℝ)) ∧
    ∀ j k, j≠k → ¬ReferenceClasses.related A.1 (a j) (a k)

lemma currentClassSelection_measurable {d : ℕ} (e : Direction d) (n : ℕ) (r : ℝ)
    (a : Fin n → ℕ) : MeasurableSet {A : CurrentData e | CurrentClassSelection e n r A a} := by
  unfold CurrentClassSelection
  change MeasurableSet ({A : CurrentData e | ∀ j, r≤(A.2 (a j,0):ℝ)} ∩
    {A : CurrentData e | ∀ j k, j≠k → ¬ReferenceClasses.related A.1 (a j) (a k)})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le measurable_const
      (((measurable_pi_apply (a j,0)).comp measurable_snd).subtype_val)
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      ((ReferenceClasses.measurable_related (a j) (a k)).preimage measurable_fst).compl

noncomputable def currentSelect {d : ℕ} (e : Direction d) (n : ℕ) (r : ℝ) : CurrentData e → Fin n → ℕ :=
  Classical.choose (measurable_countable_selection (CurrentClassSelection e n r)
    (currentClassSelection_measurable e n r))

lemma currentSelect_measurable {d : ℕ} (e : Direction d) (n : ℕ) (r : ℝ) :
    Measurable (currentSelect e n r) :=
  (Classical.choose_spec (measurable_countable_selection (CurrentClassSelection e n r)
    (currentClassSelection_measurable e n r))).1

lemma currentSelect_spec {d : ℕ} (e : Direction d) (n : ℕ) (r : ℝ) (A : CurrentData e)
    (h : ∃ a, CurrentClassSelection e n r A a) : CurrentClassSelection e n r A (currentSelect e n r A) :=
  (Classical.choose_spec (measurable_countable_selection (CurrentClassSelection e n r)
    (currentClassSelection_measurable e n r))).2 A h

lemma current_selection_event_measurable {d : ℕ} (e : Direction d) (n : ℕ) (r : ℝ) :
    MeasurableSet {A : CurrentData e | ∃ a, CurrentClassSelection e n r A a} := by
  simpa only [Set.ofPred_exists] using MeasurableSet.iUnion (currentClassSelection_measurable e n r)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience.ReferenceClasses
variable {H R : Type*} [AddCommGroup H] [Countable H] [TopologicalSpace H]
  [DiscreteTopology H] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)] [MeasurableSpace R]

lemma reference_distinct_product {n : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (O : Data H) (a : Fin n → ℕ)
    (ha : ∀ i j, i≠j → ¬related O (a i) (a j))
    (F : UpperField H R → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ φ, ∏ j : Fin n, F (fun p => φ (a j,p)) ∂reference ν O)=
      (∫⁻ ξ, F ξ ∂Measure.infinitePi (fun _ : ℕ×H => ν))^n := by
  let g : AllFields H R → (Fin n × (ℕ×H) → R) := fun φ p => φ (a p.1,p.2)
  have hg : Measurable g := by unfold g; fun_prop
  let P := Measure.infinitePi (fun _ : ℕ×H => ν)
  let M := Measure.infinitePi (fun _ : Fin n => P)
  have he := reference_distinct_classes ν O a ha
  change (reference ν O).map g = _ at he
  have hprod : Measurable (fun ξ : (Fin n × (ℕ×H) → R) => ∏ j : Fin n, F (fun p => ξ (j,p))) :=
    Finset.measurable_prod Finset.univ fun j _ => hF.comp
      (Measurable.of_eval fun position => measurable_pi_apply (j,position))
  rw [show (∫⁻ φ, ∏ j : Fin n, F (fun p => φ (a j,p)) ∂reference ν O)=
      ∫⁻ ξ, ∏ j : Fin n, F (fun p => ξ (j,p)) ∂(reference ν O).map g from
      (lintegral_map hprod hg).symm,he]
  rw [←Measure.infinitePi_map_curry_symm (fun (_ : Fin n) (_ : ℕ×H) => ν),
    lintegral_map hprod (MeasurableEquiv.curry (Fin n) (ℕ×H) R).symm.measurable]
  change (∫⁻ ξ, ∏ j : Fin n, F (ξ j) ∂M)=_
  have hind : iIndepFun (fun j (ξ : Fin n → UpperField H R) => F (ξ j)) M :=
    iIndepFun_infinitePi (X := fun (_ : Fin n) ξ => F ξ) (fun _ => hF)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun j (ξ : Fin n → UpperField H R) => F (ξ j)) hind
      (fun j => hF.comp (measurable_pi_apply j))]
  have hm (j : Fin n) : (∫⁻ ξ, F (ξ j) ∂M)=∫⁻ ξ, F ξ ∂P := by
    have hp := measurePreserving_eval_infinitePi (fun _ : Fin n => P) j
    rw [←lintegral_map hF hp.measurable,hp.map_eq]
  simp only [hm,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rfl

end DirectionalTransience.ReferenceClasses

end

end OAI
