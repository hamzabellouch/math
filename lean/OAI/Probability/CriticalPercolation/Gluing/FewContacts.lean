import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelCutProbability
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelContactMeasurability

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem few_contacts_cost (hlocal : G.LocallyFinite) (q : E → unitInterval)
    (π : V → ℤ) (j : ℤ) (o : V) (ho : j ≤ π o)
    (hcross : ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (p : unitInterval)
    (hq : ∀ e v w, G.ends e=s(v,w) → π v=j → π w<j → (q e : ℝ) ≤ p)
    (D k : ℕ) (hD : ∀ v, π v=j → (G.incidentEdges {v}).ncard ≤ D) :
    (1-(p : ℝ))^(D*k)*(BernoulliProduct.law q).real (G.fewContacts π j o k) ≤
      (BernoulliProduct.law q).real (G.minimumLevel π o j) := by
  let X := G.inducedEdges {v | j ≤ π v}
  let d : Set E → Finset E := fun ω => finiteSetChoice (G.contactDrop π j o ω)
  let A : Finset E → Set (Set E) := fun U => closedBlock ((U : Set E)∩Xᶜ)
  have hd (U : Finset E) : MeasurableSet[blockSigma X] {ω | d ω=U} :=
    @measurableSet_finiteSetChoice (Set E) E (blockSigma X) inferInstance
      (G.contactDrop π j o) (G.measurable_contactDrop π j o) U
  have hA (U : Finset E) : MeasurableSet[blockSigma Xᶜ] (A U) :=
    (blockSigma_mono Set.inter_subset_right) _
      (measurableSet_closedBlock _ ((U.finite_toSet.subset Set.inter_subset_left).countable))
  have he (ω : Set E) (hω : ω∈G.fewContacts π j o k) :
      ((d ω : Set E)∩Xᶜ)=G.contactDrop π j o ω := by
    rw [finiteSetChoice_coe (G.finite_contactDrop hlocal π j o ω
      (G.fewContacts_finite π j o k ω hω).1)]
    exact Set.inter_eq_left.mpr (Set.disjoint_left.mp
      (G.contactDrop_disjoint_exterior π j o ω))
  have hb (ω : Set E) (hω : ω∈G.fewContacts π j o k) :
      (1-(p : ℝ))^(D*k) ≤ (BernoulliProduct.law q).real (A (d ω)) := by
    change _ ≤ (BernoulliProduct.law q).real (closedBlock ((d ω : Set E)∩Xᶜ))
    rw [he ω hω]
    have hω' := G.fewContacts_finite π j o k ω hω
    apply law_closedBlock_lower q _ (G.finite_contactDrop hlocal π j o ω hω'.1) p
    · calc
        _ ≤ (G.levelContacts π j o ω).ncard*D :=
          G.contactDrop_ncard_le hlocal π j o ω hω'.1 D (fun v hv => hD v hv.2)
        _ ≤ k*D := Nat.mul_le_mul_right D (Nat.le_of_lt hω'.2.2)
        _ = D*k := Nat.mul_comm _ _
    · rintro e ⟨v,hv,w,hw,hend⟩
      exact hq e v w hend hv.2 hw
  have hh := selected_fresh_lower q X Xᶜ disjoint_compl_right d A hd hA
    (G.fewContacts π j o k) (G.measurableSet_fewContacts π j o k)
    ((1-(p : ℝ))^(D*k)) (pow_nonneg (sub_nonneg.mpr p.2.2) _) hb
  apply hh.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro ω ⟨hω,hclosed⟩
  apply G.minimumLevel_of_drop_closed π j o ho hcross ω
    (G.fewContacts_finite π j o k ω hω).2.1
  change Disjoint ((d ω : Set E)∩Xᶜ) ω at hclosed
  rwa [he ω hω] at hclosed

theorem exists_few_contact_level (hlocal : G.LocallyFinite) (q : E → unitInterval)
    (π : V → ℤ) (o : V) (J : Finset ℤ) (hJ : J.Nonempty)
    (ho : ∀ j∈J, j ≤ π o)
    (hcross : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (p : unitInterval) (hp : (p : ℝ)<1)
    (hq : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → π v=j → π w<j → (q e : ℝ) ≤ p)
    (D k : ℕ) (hD : ∀ j∈J, ∀ v, π v=j → (G.incidentEdges {v}).ncard ≤ D) :
    ∃ j∈J, (BernoulliProduct.law q).real (G.fewContacts π j o k) ≤
      1/((J.card : ℝ)*(1-(p : ℝ))^(D*k)) := by
  apply exists_level_small (BernoulliProduct.law q) J hJ (fun j => G.fewContacts π j o k)
    (G.minimumLevel π o) (fun j _ => G.measurableSet_minimumLevel π o j)
  · intro i hi j hj hij
    exact G.minimumLevel_pairwiseDisjoint π o hij
  · exact pow_pos (sub_pos.mpr hp) _
  · intro j hj
    exact G.few_contacts_cost hlocal q π j o (ho j hj) (hcross j hj) p (hq j hj) D k (hD j hj)

end CriticalPercolation.BondGraph
end
end
end

end OAI
