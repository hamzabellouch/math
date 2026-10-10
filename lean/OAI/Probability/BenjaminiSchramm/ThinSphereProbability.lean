import OAI.Probability.BenjaminiSchramm.ThinSphereStopping
import OAI.Probability.BenjaminiSchramm.LayerFreshSelection

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem domainRadiusEvent_dependsOn (G : BondGraph V E) (S : Set E) (x : V) (n : ℕ) :
    DependsOn (fun ω => ω ∈ domainRadiusEvent G S x n) S := by
  intro ω η hagree
  have he : Set.inter ω S = Set.inter η S := by
    apply Set.ext
    intro e
    change (ω e ∧ e ∈ S) ↔ (η e ∧ e ∈ S)
    by_cases he : e ∈ S
    · simp only [he,and_true]
      exact (hagree e he).to_iff
    · simp only [he,and_false]
  change (Set.inter ω S ∈ intrinsicRadiusEvent G x n) =
    (Set.inter η S ∈ intrinsicRadiusEvent G x n)
  exact congrArg (fun B : Set E => B ∈ intrinsicRadiusEvent G x n) he

theorem activeThinSphereCell_fresh_factor [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (S : Set E) (x : V) (r k j : ℕ) (hr : 0 < r) (U W : Finset V) (z : V) :
    law p (activeThinSphereCell G S x r k j U W ∩
      domainRadiusEvent G (S \ ballIncidentEdges G U) z r) =
      law p (activeThinSphereCell G S x r k j U W) *
        law p (domainRadiusEvent G (S \ ballIncidentEdges G U) z r) := by
  unfold law
  rw [←CriticalPercolation.BernoulliProduct.law_const]
  apply CriticalPercolation.BernoulliProduct.measure_inter_of_separate_blocks
    (fun _ => p) (ballIncidentEdges G U) _ _
    (measurableSet_activeThinSphereCell G hloc S x r k j hr U W)
    (measurableSet_domainRadiusEvent G hloc _ z r)
    (activeThinSphereCell_dependsOn G S x r k j hr U W)
  intro ω η hagree
  apply domainRadiusEvent_dependsOn G (S \ ballIncidentEdges G U) z r
  intro e he
  exact hagree e he.2

theorem activeThinSphereCell_continuation (G : BondGraph V E) (S ω : Set E)
    (x : V) (r k j : ℕ) (hr : 0 < r) (U W : Finset V)
    (hcell : ω ∈ activeThinSphereCell G S x r k j U W)
    (hR : ω ∈ domainRadiusEvent G S x (3*r)) :
    ∃ z ∈ W \ U, ω ∈ domainRadiusEvent G (S \ ballIncidentEdges G U) z r := by
  have hj0 : 0 < j := hr.trans_le hcell.1.1
  have hj2 : j ≤ 2*r := hcell.1.2.1
  have hRjr : ω ∩ S ∈ intrinsicRadiusEvent G x (j+r) := by
    obtain ⟨y,hc,hd⟩ := hR
    exact ⟨y,hc,(by omega : j+r ≤ 3*r).trans hd⟩
  obtain ⟨z,hz,hfresh⟩ := intrinsic_radius_fresh_continuation G (ω ∩ S) x j r hj0 hRjr
  have hU := hcell.1.2.2.1
  have hW := hcell.1.2.2.2.1
  have hzWU : z ∈ W \ U := by
    rw [intrinsicSphere_eq_ball_sdiff G _ x j hj0,hU,hW] at hz
    exact_mod_cast hz
  refine ⟨z,hzWU,?_⟩
  change ω ∩ (S \ ballIncidentEdges G U) ∈ intrinsicRadiusEvent G z r
  rw [hU] at hfresh
  have he : (ω ∩ S) \ ballIncidentEdges G U = ω ∩ (S \ ballIncidentEdges G U) := by
    ext e; simp only [Set.mem_sdiff,Set.mem_inter_iff]; tauto
  rw [he] at hfresh
  exact hfresh

theorem activeThinSphereCell_frontier_card (G : BondGraph V E) (S ω : Set E)
    (x : V) (r k j : ℕ) (hr : 0 < r) (U W : Finset V)
    (hcell : ω ∈ activeThinSphereCell G S x r k j U W) : (W \ U).card ≤ k := by
  have hthin := hcell.1.2.2.2.2.1
  rw [intrinsicSphere_eq_ball_sdiff G _ x j (hr.trans_le hcell.1.1),
    hcell.1.2.2.1,hcell.1.2.2.2.1,←Finset.coe_sdiff,Set.ncard_coe_finset] at hthin
  exact hthin

theorem activeThinSphereCell_survival_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (S : Set E) (x : V) (r k j : ℕ) (hr : 0 < r) (U W : Finset V)
    (b : ℝ≥0∞) (hb : ∀ (I : Set E) z, law p (domainRadiusEvent G I z r) ≤ b) :
    law p (activeThinSphereCell G S x r k j U W ∩ domainRadiusEvent G S x (3*r)) ≤
      law p (activeThinSphereCell G S x r k j U W) * k * b := by
  let A := activeThinSphereCell G S x r k j U W
  by_cases hA : A.Nonempty
  · obtain ⟨ω,hω⟩ := hA
    have hcard := activeThinSphereCell_frontier_card G S ω x r k j hr U W hω
    have hsub : A ∩ domainRadiusEvent G S x (3*r) ⊆
        ⋃ z ∈ W \ U, A ∩ domainRadiusEvent G (S \ ballIncidentEdges G U) z r := by
      rintro η ⟨hη,hR⟩
      obtain ⟨z,hz,hfresh⟩ := activeThinSphereCell_continuation G S η x r k j hr U W hη hR
      exact Set.mem_iUnion.mpr ⟨z,Set.mem_iUnion.mpr ⟨hz,hη,hfresh⟩⟩
    calc
      _ ≤ law p (⋃ z ∈ W \ U, A ∩ domainRadiusEvent G (S \ ballIncidentEdges G U) z r) := measure_mono hsub
      _ ≤ ∑ z ∈ W \ U, law p (A ∩ domainRadiusEvent G (S \ ballIncidentEdges G U) z r) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ W \ U, law p A * b := by
        apply Finset.sum_le_sum
        intro z _
        rw [activeThinSphereCell_fresh_factor G hloc p S x r k j hr U W z]
        exact mul_le_mul' le_rfl (hb _ z)
      _ = law p A * (W \ U).card * b := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl (by exact_mod_cast hcard)) le_rfl
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    change law p (A ∩ _) ≤ law p A * _ * _
    rw [he]
    simp

end Percolation.BenjaminiSchramm

end OAI
