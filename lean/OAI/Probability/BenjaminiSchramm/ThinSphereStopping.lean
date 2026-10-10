import OAI.Probability.BenjaminiSchramm.ThinSphereExposure
import OAI.Probability.BenjaminiSchramm.IntrinsicFreshPath

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def domainRadiusEvent (G : BondGraph V E) (S : Set E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ω ∩ S ∈ intrinsicRadiusEvent G x n}

def activeThinSphereCell (G : BondGraph V E) (S : Set E) (x : V) (r k j : ℕ)
    (U W : Finset V) : Set (Set E) :=
  thinSphereCell G S x r k j U W ∩ domainRadiusEvent G S x r

theorem measurableSet_domainRadiusEvent [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (S : Set E) (x : V) (n : ℕ) :
    MeasurableSet (domainRadiusEvent G S x n) := by
  have hm : Measurable (fun ω : Set E => ω ∩ S) :=
    measurable_set_iff.mpr (fun e => (measurable_set_mem e).and measurable_const)
  exact (measurableSet_intrinsicRadiusEvent G hloc x n).preimage hm

theorem measurableSet_activeThinSphereCell [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (S : Set E) (x : V)
    (r k j : ℕ) (hr : 0 < r) (U W : Finset V) :
    MeasurableSet (activeThinSphereCell G S x r k j U W) :=
  (measurableSet_thinSphereCell G hloc S x r k j hr U W).inter
    (measurableSet_domainRadiusEvent G hloc S x r)

theorem activeThinSphereCell_pairwise (G : BondGraph V E) (S : Set E) (x : V) (r k : ℕ) :
    Pairwise (fun a b : ℕ × Finset V × Finset V =>
      Disjoint (activeThinSphereCell G S x r k a.1 a.2.1 a.2.2)
        (activeThinSphereCell G S x r k b.1 b.2.1 b.2.2)) := by
  intro a b hab
  exact (thinSphereCell_pairwise G S x r k hab).mono Set.inter_subset_left Set.inter_subset_left

theorem activeThinSphereCell_dependsOn (G : BondGraph V E) (S : Set E) (x : V)
    (r k j : ℕ) (hr : 0 < r) (U W : Finset V) :
    DependsOn (fun ω => ω ∈ activeThinSphereCell G S x r k j U W) (ballIncidentEdges G U) := by
  intro ω η hagree
  apply propext
  have hforward (ω η : Set E)
      (hωη : ∀ e ∈ ballIncidentEdges G U, (e ∈ ω) = (e ∈ η))
      (hω : ω ∈ activeThinSphereCell G S x r k j U W) :
      η ∈ activeThinSphereCell G S x r k j U W := by
    have hθη := ((thinSphereCell_dependsOn G S x r k j hr U W) hωη).to_iff.mp hω.1
    have hU := hω.1.2.2.1
    have hrj := hω.1.1
    have hballs := intrinsicBall_history_eq_of_incident_agreement G (ω ∩ S) (η ∩ S) x j (by
      intro e he
      rw [hU] at he
      exact and_congr (hωη e he).to_iff Iff.rfl)
    refine ⟨hθη,?_⟩
    have hR := hω.2
    change ω ∩ S ∈ intrinsicRadiusEvent G x r at hR
    change η ∩ S ∈ intrinsicRadiusEvent G x r
    rw [intrinsicRadiusEvent_iff_sphere,intrinsicSphere_eq_ball_sdiff G _ x r hr,
      hballs r hrj,hballs (r-1) ((Nat.sub_le r 1).trans hrj)] at hR
    rw [intrinsicRadiusEvent_iff_sphere,intrinsicSphere_eq_ball_sdiff G _ x r hr]
    exact hR
  exact ⟨hforward ω η hagree,hforward η ω (fun e he => (hagree e he).symm)⟩

theorem exists_activeThinSphereCell_of_small_cluster (G : BondGraph V E)
    (hloc : LocallyFinite G) (S ω : Set E) (x : V) (r k : ℕ)
    (hf : (cluster G (ω ∩ S) x).Finite)
    (hsmall : (cluster G (ω ∩ S) x).ncard < (r+1)*(k+1))
    (hR : ω ∈ domainRadiusEvent G S x r) :
    ∃ a : ℕ × Finset V × Finset V,
      ω ∈ activeThinSphereCell G S x r k a.1 a.2.1 a.2.2 := by
  obtain ⟨j,hj,hthin⟩ := exists_thin_intrinsicSphere G hloc (ω ∩ S) x r k hf hsmall
  have hex : ∃ j : ℕ, r ≤ j ∧ j ≤ 2*r ∧ (intrinsicSphere G (ω ∩ S) x j).ncard ≤ k :=
    ⟨j,(Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2,hthin⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  let hU := (finite_reachBall hloc x (j-1)).subset (intrinsicBall_subset_reachBall G (ω ∩ S) x (j-1))
  let hW := (finite_reachBall hloc x j).subset (intrinsicBall_subset_reachBall G (ω ∩ S) x j)
  refine ⟨(j,hU.toFinset,hW.toFinset),?_,hR⟩
  refine ⟨hj.1,hj.2.1,hU.coe_toFinset.symm,hW.coe_toFinset.symm,hj.2.2,?_⟩
  intro i hri hij
  by_contra hki
  have hi := Nat.find_min hex hij
  exact hi ⟨hri,(by omega),Nat.le_of_not_gt hki⟩

end Percolation.BenjaminiSchramm

end OAI
