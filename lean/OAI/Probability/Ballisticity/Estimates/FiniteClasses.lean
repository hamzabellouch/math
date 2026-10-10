import Mathlib
import OAI.Probability.Ballisticity.Estimates.ClassSelection

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def CurrentFiniteClasses {d : ℕ} (e : Direction d) (A : CurrentData e) : Prop :=
  (Set.range (ReferenceClasses.representative A.1)).Finite

lemma currentFiniteClasses_measurable {d : ℕ} (e : Direction d) :
    MeasurableSet {A : CurrentData e | CurrentFiniteClasses e A} := by
  have he : {A : CurrentData e | CurrentFiniteClasses e A} =
      {A | ∃ N : ℕ, ∀ a, ReferenceClasses.representative A.1 a≤N} := by
    ext A
    change CurrentFiniteClasses e A ↔ _
    rw [CurrentFiniteClasses,Set.finite_iff_bddAbove]
    constructor
    · rintro ⟨N,hN⟩
      exact ⟨N,fun a => hN (Set.mem_range_self a)⟩
    · rintro ⟨N,hN⟩
      exact ⟨N,by rintro _ ⟨a,rfl⟩; exact hN a⟩
  rw [he]
  simp only [Set.ofPred_exists,Set.ofPred_forall]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun a =>
    measurableSet_le ((ReferenceClasses.measurable_representative a).comp measurable_fst) measurable_const

lemma infinite_current_selection_eventually {d : ℕ} (e : Direction d) (A : CurrentData e)
    (hfin : ¬CurrentFiniteClasses e A) (hproper : ∀ a, 0<(A.2 (a,0):ℝ)) (n : ℕ) :
    ∀ᶠ (k : ℕ) in atTop, ∃ a, CurrentClassSelection e n (1/((k:ℝ)+1)) A a := by
  let S := Set.range (ReferenceClasses.representative A.1)
  have hS : S.Infinite := hfin
  let emb := hS.natEmbedding S
  let a : Fin n → ℕ := fun j => (emb j.val).val
  have ha (j : Fin n) : ReferenceClasses.representative A.1 (a j)=a j := by
    obtain ⟨b,hb⟩ := (emb j.val).property
    change ReferenceClasses.representative A.1 ((emb j.val).val)=(emb j.val).val
    rw [←hb]
    exact (ReferenceClasses.representative_eq_iff A.1 _ _).mpr (ReferenceClasses.representative_related A.1 b)
  have hsep (j k : Fin n) (hjk : j≠k) : ¬ReferenceClasses.related A.1 (a j) (a k) := by
    intro h
    have hh := (ReferenceClasses.representative_eq_iff A.1 _ _).mpr h
    rw [ha,ha] at hh
    have hjk' := emb.injective (Subtype.ext hh)
    exact hjk (Fin.ext hjk')
  have ht : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    have hn : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop := (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    exact hn.const_div_atTop 1
  have hj (j : Fin n) : ∀ᶠ (k : ℕ) in atTop, 1/((k:ℝ)+1)≤(A.2 (a j,0):ℝ) :=
    ht.eventually (ge_mem_nhds (hproper (a j)))
  filter_upwards [eventually_all.mpr hj] with k hk
  exact ⟨a,hk,hsep⟩

end DirectionalTransience

end

end OAI
