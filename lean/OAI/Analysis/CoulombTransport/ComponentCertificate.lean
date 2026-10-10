import OAI.Analysis.CoulombTransport.CertificateNeighborhoods
import OAI.Analysis.CoulombTransport.ComponentPotential
import OAI.Analysis.CoulombTransport.CostTopology

namespace OAI

universe uIndex

noncomputable section
open Set Filter Metric
open scoped ENNReal BigOperators

namespace Problem356

/-- Every bad center type with a strict extended-valued cost gap retains that
gap on small component balls. The finite index set may include repeated-center
types, since extended-valued Coulomb cost is continuous at collisions. -/
theorem finite_bad_component_neighborhoods {ι : Type uIndex}
    (s : Finset (ι × (ι × ι))) (p : ι → E3) (v : ι → E3 → ℝ)
    (hv : ∀ i, ContinuousAt (v i) (p i))
    (hgap : ∀ a ∈ s,
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ s, ∀ x y z : E3,
      x ∈ ball (p a.1) r → y ∈ ball (p a.2.1) r → z ∈ ball (p a.2.2) r →
      ENNReal.ofReal (v a.1 x + v a.2.1 y + v a.2.2 z) <
        coulombCost (x, (y, z)) := by
  apply finite_strict_triple_neighborhoods s
    (fun a => (p a.1, (p a.2.1, p a.2.2)))
    (fun a t => ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2))
    (fun _ => coulombCost)
  · intro a _
    have h₁ : ContinuousAt (fun t : Triple => v a.1 t.1)
        (p a.1, (p a.2.1, p a.2.2)) :=
      (hv a.1).comp (f := fun t : Triple => t.1) continuousAt_fst
    have h₂ : ContinuousAt (fun t : Triple => v a.2.1 t.2.1)
        (p a.1, (p a.2.1, p a.2.2)) :=
      (hv a.2.1).comp (f := fun t : Triple => t.2.1)
        (continuousAt_fst.comp continuousAt_snd)
    have h₃ : ContinuousAt (fun t : Triple => v a.2.2 t.2.2)
        (p a.1, (p a.2.1, p a.2.2)) :=
      (hv a.2.2).comp (f := fun t : Triple => t.2.2)
        (continuousAt_snd.comp continuousAt_snd)
    exact ENNReal.continuous_ofReal.continuousAt.comp ((h₁.add h₂).add h₃)
  · intro _ _
    exact continuous_coulombCost.continuousAt
  · exact hgap

/-- Continuity of the sum of the three local potentials in one component type. -/
theorem continuousAt_component_sum {ι : Type uIndex} (p : ι → E3) (v : ι → E3 → ℝ)
    (hv : ∀ i, ContinuousAt (v i) (p i)) (a : ι × (ι × ι)) :
    ContinuousAt
      (fun t : Triple => ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2))
      (p a.1, (p a.2.1, p a.2.2)) := by
  have h₁ : ContinuousAt (fun t : Triple => v a.1 t.1)
      (p a.1, (p a.2.1, p a.2.2)) :=
    (hv a.1).comp (f := fun t : Triple => t.1) continuousAt_fst
  have h₂ : ContinuousAt (fun t : Triple => v a.2.1 t.2.1)
      (p a.1, (p a.2.1, p a.2.2)) :=
    (hv a.2.1).comp (f := fun t : Triple => t.2.1)
      (continuousAt_fst.comp continuousAt_snd)
  have h₃ : ContinuousAt (fun t : Triple => v a.2.2 t.2.2)
      (p a.1, (p a.2.1, p a.2.2)) :=
    (hv a.2.2).comp (f := fun t : Triple => t.2.2)
      (continuousAt_snd.comp continuousAt_snd)
  exact ENNReal.continuous_ofReal.continuousAt.comp ((h₁.add h₂).add h₃)

/-- The local-to-global finite-type certificate step. Local supporting
inequalities and exact contact sets are needed only at the good types;
strict gaps at every other center type are enough for all remaining types.
A single radius works for the inequalities and exact equality characterization. -/
theorem finite_component_certificate {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (v : ι → E3 → ℝ)
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop)
    (hv : ∀ i, ContinuousAt (v i) (p i))
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Contact a t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r : ℝ, 0 < r ∧ ∀ a, ∀ x y z : E3,
      x ∈ ball (p a.1) r → y ∈ ball (p a.2.1) r → z ∈ ball (p a.2.2) r →
      ENNReal.ofReal (v a.1 x + v a.2.1 y + v a.2.2 z) ≤ coulombCost (x, (y, z)) ∧
      (ENNReal.ofReal (v a.1 x + v a.2.1 y + v a.2.2 z) = coulombCost (x, (y, z)) ↔
        Good a ∧ Contact a (x, (y, z))) := by
  classical
  have hevent : ∀ a ∈ (Finset.univ : Finset (ι × (ι × ι))),
      ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Good a ∧ Contact a t) := by
    intro a _
    by_cases ha : Good a
    · filter_upwards [hgood a ha] with t ht
      exact ⟨ht.1, by simpa [ha] using ht.2⟩
    · have he := (continuousAt_component_sum p v hv a).eventually_lt
        continuous_coulombCost.continuousAt (hbad a ha)
      filter_upwards [he] with t ht
      exact ⟨ht.le, by simp [ha, ht.ne]⟩
  obtain ⟨r, hr, h⟩ := finite_eventual_triple_neighborhoods Finset.univ
    (fun a : ι × (ι × ι) => (p a.1, (p a.2.1, p a.2.2))) _ hevent
  exact ⟨r, hr, fun a => h a (Finset.mem_univ a)⟩

/-- Once all ordered component types have been certified, the glued potential
satisfies the supporting inequality on the entire component union. -/
theorem componentPotential_supporting_inequality {ι : Type uIndex} [Fintype ι]
    (U : ι → Set E3) (v : ι → E3 → ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hlocal : ∀ i j k, ∀ x ∈ U i, ∀ y ∈ U j, ∀ z ∈ U k,
      ENNReal.ofReal (v i x + v j y + v k z) ≤ coulombCost (x, (y, z)))
    {x y z : E3} (hx : x ∈ ⋃ i, U i) (hy : y ∈ ⋃ i, U i)
    (hz : z ∈ ⋃ i, U i) :
    ENNReal.ofReal (ComponentPotential.glue U v x + ComponentPotential.glue U v y +
      ComponentPotential.glue U v z) ≤ coulombCost (x, (y, z)) := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz
  rw [ComponentPotential.glue_eq hdisj hi, ComponentPotential.glue_eq hdisj hj,
    ComponentPotential.glue_eq hdisj hk]
  exact hlocal i j k x hi y hj z hk

/-- Strict inequalities on bad ordered component types exclude those types
from the contact set of the glued potential. -/
theorem componentPotential_contact_good {ι : Type uIndex} [Fintype ι]
    (U : ι → Set E3) (v : ι → E3 → ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (Good : ι → ι → ι → Prop)
    (hbad : ∀ i j k, ¬ Good i j k → ∀ x ∈ U i, ∀ y ∈ U j, ∀ z ∈ U k,
      ENNReal.ofReal (v i x + v j y + v k z) < coulombCost (x, (y, z)))
    {i j k : ι} {x y z : E3} (hx : x ∈ U i) (hy : y ∈ U j) (hz : z ∈ U k)
    (hcontact : ENNReal.ofReal (ComponentPotential.glue U v x + ComponentPotential.glue U v y +
      ComponentPotential.glue U v z) = coulombCost (x, (y, z))) : Good i j k := by
  classical
  by_contra hnot
  have hlt := hbad i j k hnot x hx y hy z hz
  rw [ComponentPotential.glue_eq hdisj hx, ComponentPotential.glue_eq hdisj hy,
    ComponentPotential.glue_eq hdisj hz] at hcontact
  exact (ne_of_lt hlt) hcontact

end Problem356

end

end OAI
