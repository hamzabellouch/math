import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Encounter.NearestMass
import OAI.Probability.UnimodularPercolation.Encounter.Transport

namespace OAI

/-! Encounter vertices and infinite open branches. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

def cutConfig (G : BondGraph V E) (ω : Set E) (x : V) : Set E :=
  {e | e ∈ ω ∧ x ∉ G e}

theorem measurable_cutConfig (G : BondGraph V E) (x : V) :
    Measurable (fun ω => cutConfig G ω x) := by
  apply measurable_setOfPred.comp (Measurable.of_eval ?_)
  intro e
  exact (measurable_set_mem e).and measurable_const

theorem cutVertex_open (G : BondGraph V E) (ω : Set E) (x : V) :
    cutVertex (openSimpleGraph G ω) x = openSimpleGraph G (cutConfig G ω x) := by
  ext a b
  change ((a ≠ b ∧ ∃ e ∈ ω, G e = s(a,b)) ∧ a ≠ x ∧ b ≠ x) ↔
    (a ≠ b ∧ ∃ e, (e ∈ ω ∧ x ∉ G e) ∧ G e = s(a,b))
  constructor
  · rintro ⟨⟨hab,e,he,hGe⟩,hax,hbx⟩
    exact ⟨hab,e,⟨he,by rw [hGe]; simpa [Sym2.mem_iff,eq_comm] using And.intro hax hbx⟩,hGe⟩
  · rintro ⟨hab,e,⟨he,hx⟩,hGe⟩
    rw [hGe] at hx
    have hh : a ≠ x ∧ b ≠ x := by simpa [Sym2.mem_iff,eq_comm] using hx
    exact ⟨⟨hab,e,he,hGe⟩,hh⟩

theorem cutConfig_aut (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    cutConfig G (b ⁻¹' ω) x = b ⁻¹' cutConfig G ω (a x) := by
  ext e
  simp only [cutConfig,Set.mem_ofPred_eq,Set.mem_preimage,hab e]
  rw [Sym2.mem_map]
  simp only [a.injective.eq_iff,exists_eq_right]

def IsEncounter (G : BondGraph V E) (ω : Set E) (x : V) : Prop :=
  ∃ a b c : V,
    Conn G ω x a ∧ Conn G ω x b ∧ Conn G ω x c ∧
    (cluster G (cutConfig G ω x) a).Infinite ∧
    (cluster G (cutConfig G ω x) b).Infinite ∧
    (cluster G (cutConfig G ω x) c).Infinite ∧
    ¬ Conn G (cutConfig G ω x) a b ∧
    ¬ Conn G (cutConfig G ω x) a c ∧
    ¬ Conn G (cutConfig G ω x) b c

def encounters (G : BondGraph V E) (ω : Set E) : Set V := {x | IsEncounter G ω x}

theorem measurableSet_isEncounter [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) : MeasurableSet {ω | IsEncounter G ω x} := by
  simp only [IsEncounter,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  apply MeasurableSet.iUnion
  intro c
  exact (measurableSet_conn G x a).inter ((measurableSet_conn G x b).inter
    ((measurableSet_conn G x c).inter
      (((measurableSet_infinite_cluster G a).preimage (measurable_cutConfig G x)).inter
      (((measurableSet_infinite_cluster G b).preimage (measurable_cutConfig G x)).inter
      (((measurableSet_infinite_cluster G c).preimage (measurable_cutConfig G x)).inter
      (((measurableSet_conn G a b).preimage (measurable_cutConfig G x)).compl.inter
      (((measurableSet_conn G a c).preimage (measurable_cutConfig G x)).compl.inter
      ((measurableSet_conn G b c).preimage (measurable_cutConfig G x)).compl)))))))

theorem isEncounter_aut_iff (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    IsEncounter G (b ⁻¹' ω) x ↔ IsEncounter G ω (a x) := by
  have hc y z : Conn G (cutConfig G (b ⁻¹' ω) x) y z ↔
      Conn G (cutConfig G ω (a x)) (a y) (a z) := by
    rw [cutConfig_aut G a b hab]
    exact conn_aut_iff G hab _ y z
  have hi y : (cluster G (cutConfig G (b ⁻¹' ω) x) y).Infinite ↔
      (cluster G (cutConfig G ω (a x)) (a y)).Infinite := by
    rw [cutConfig_aut G a b hab,←cluster_aut G hab]
    exact (Set.infinite_image_iff a.injective.injOn).symm
  constructor
  · rintro ⟨u,v,w,hxu,hxv,hxw,hu,hv,hw,huv,huw,hvw⟩
    exact ⟨a u,a v,a w,(conn_aut_iff G hab ω x u).mp hxu,
      (conn_aut_iff G hab ω x v).mp hxv,(conn_aut_iff G hab ω x w).mp hxw,
      (hi u).mp hu,(hi v).mp hv,(hi w).mp hw,
      fun h => huv ((hc u v).mpr h),fun h => huw ((hc u w).mpr h),fun h => hvw ((hc v w).mpr h)⟩
  · rintro ⟨u,v,w,hxu,hxv,hxw,hu,hv,hw,huv,huw,hvw⟩
    refine ⟨a.symm u,a.symm v,a.symm w,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (conn_aut_iff G hab ω x _).mpr (by simpa using hxu)
    · exact (conn_aut_iff G hab ω x _).mpr (by simpa using hxv)
    · exact (conn_aut_iff G hab ω x _).mpr (by simpa using hxw)
    · exact (hi _).mpr (by simpa using hu)
    · exact (hi _).mpr (by simpa using hv)
    · exact (hi _).mpr (by simpa using hw)
    · intro h; exact huv (by simpa using (hc _ _).mp h)
    · intro h; exact huw (by simpa using (hc _ _).mp h)
    · intro h; exact hvw (by simpa using (hc _ _).mp h)

theorem encounter_branch_contains_of_finite_incoming (G : BondGraph V E)
    (ω : Set E) (x a : V) (hx : IsEncounter G ω x) (hxa : Conn G ω x a)
    (hInf : (cluster G (cutConfig G ω x) a).Infinite)
    (hin : ∑' y, nearestMass G (encounters G) ω y x < ⊤) :
    ∃ z ∈ cluster G (cutConfig G ω x) a, z ≠ x ∧ IsEncounter G ω z := by
  by_contra hno
  have hm (y : V) (hy : y ∈ cluster G (cutConfig G ω x) a) :
      nearestMass G (encounters G) ω y x = 1 := by
    apply nearestMass_eq_one
    apply closest_eq_singleton_of_branch (openSimpleGraph G ω) (encounters G ω) hx
    · apply (conn_iff_reachable G ω y x).mp
      exact conn_symm G ω (conn_trans G ω hxa (conn_mono G (fun e he => he.1) hy))
    · intro z hz hzx hcut
      apply hno
      refine ⟨z,?_,hzx,hz⟩
      rw [cutVertex_open] at hcut
      exact conn_trans G _ hy ((conn_iff_reachable G _ y z).mpr hcut)
  have he := incoming_top_of_infinite (fun y => nearestMass G (encounters G) ω y x)
    (cluster G (cutConfig G ω x) a) hInf hm
  rw [he] at hin
  exact lt_irrefl _ hin

theorem encounter_branches_ae [Countable V] [Countable E] [Fintype ι]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x) (p : unitInterval) :
    ∀ᵐ ω ∂law p, ∀ x, IsEncounter G ω x → ∀ a, Conn G ω x a →
      (cluster G (cutConfig G ω x) a).Infinite →
      ∃ z ∈ cluster G (cutConfig G ω x) a, z ≠ x ∧ IsEncounter G ω z := by
  have hin := incoming_finite_ae_all G hconn hloc root weight htr hw hw1 hcov p
    (nearestMass G (encounters G))
    (measurable_nearestMass G (encounters G) (measurableSet_isEncounter G))
    (nearestMass_aut G (encounters G) (isEncounter_aut_iff G))
    (nearestMass_row_le G hloc (encounters G))
  filter_upwards [hin] with ω hω
  intro x hx a hxa hi
  exact encounter_branch_contains_of_finite_incoming G ω x a hx hxa hi (hω x)

end Percolation

end OAI
