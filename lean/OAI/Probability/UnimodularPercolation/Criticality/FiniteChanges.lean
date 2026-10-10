import Mathlib
import OAI.Probability.UnimodularPercolation.Main

namespace OAI

/-! Finite changes of bond configurations and their positive probabilities. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def finiteOverwrite (F P : Finset E) (ω : Set E) : Set E :=
  (ω ∩ (F:Set E)ᶜ) ∪ (P:Set E)

theorem measurable_finiteOverwrite (F P : Finset E) : Measurable (finiteOverwrite F P) :=
  (measurable_union_const (P:Set E)).comp (measurable_inter_const (F:Set E)ᶜ)

theorem finite_pattern_pos [Countable E] (p : unitInterval) (hp : 0 < p) (hp1 : p < 1)
    (F P : Finset E) (hPF : P ⊆ F) :
    0 < (law p : Measure (Set E)) {ω | ω ∩ (F:Set E) = (P:Set E)} := by
  let R : Set (F:Set E) := Subtype.val ⁻¹' (P:Set E)
  have he : {ω : Set E | ω ∩ (F:Set E) = (P:Set E)} =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (F:Set E))) ⁻¹' {R} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro h
      ext e
      change e.val ∈ ω ↔ e.val ∈ (P:Set E)
      have := Set.ext_iff.mp h e.val
      simpa only [Set.mem_inter_iff,e.property,and_true] using this
    · intro h
      ext e
      simp only [Set.mem_inter_iff,Finset.mem_coe]
      constructor
      · rintro ⟨he,hF⟩
        exact (Set.ext_iff.mp h ⟨e,hF⟩).mp he
      · intro he
        have hF := hPF he
        exact ⟨(Set.ext_iff.mp h ⟨e,hF⟩).mpr he,hF⟩
  rw [he,←Measure.map_apply (measurable_set_restrict _) (measurableSet_singleton _),law_map_restrict]
  have hh : 0 < (law p : Measure (Set (F:Set E))).real {R} := by
    rw [law,setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ]
    exact mul_pos (pow_pos (show (0:ℝ) < p from hp) _)
      (pow_pos (sub_pos.mpr (show (p:ℝ) < 1 from hp1)) _)
  exact (ENNReal.toReal_pos_iff.mp hh).1

theorem finiteOverwrite_pos [Countable E] (p : unitInterval) (hp : 0 < p) (hp1 : p < 1)
    (F P : Finset E) (hPF : P ⊆ F) (A B : Set (Set E))
    (hB : MeasurableSet B) (hA : 0 < (law p : Measure (Set E)) A)
    (hAB : ∀ ω ∈ A, finiteOverwrite F P ω ∈ B) : 0 < (law p : Measure (Set E)) B := by
  let D := (finiteOverwrite F P) ⁻¹' B
  let C : Set (Set E) := {ω | ω ∩ (F:Set E) = (P:Set E)}
  have hD : MeasurableSet D := hB.preimage (measurable_finiteOverwrite F P)
  have hDfix : (fun ω : Set E => ω ∩ (F:Set E)ᶜ) ⁻¹' D = D := by
    ext ω
    simp only [D,finiteOverwrite,Set.mem_preimage,Set.inter_assoc,Set.inter_self]
  have hind := restriction_events_independent p (F:Set E) (F:Set E)ᶜ disjoint_compl_right
    {(P:Set E)} D (measurableSet_singleton _) hD
  rw [hDfix] at hind
  change (law p : Measure (Set E)) (C ∩ D) = law p C * law p D at hind
  have hposC : 0 < (law p : Measure (Set E)) C := finite_pattern_pos p hp hp1 F P hPF
  have hposD : 0 < (law p : Measure (Set E)) D := hA.trans_le (measure_mono hAB)
  have hsub : C ∩ D ⊆ B := by
    rintro ω ⟨hC,hD⟩
    have he : finiteOverwrite F P ω = ω := by
      change ω ∩ (F:Set E) = (P:Set E) at hC
      rw [finiteOverwrite,←hC]
      ext e
      simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]
      tauto
    simpa only [D,Set.mem_preimage,he] using hD
  apply lt_of_lt_of_le _ (measure_mono hsub)
  rw [hind]
  exact ENNReal.mul_pos hposC.ne' hposD.ne'

theorem infinite_cluster_union_contains (G : BondGraph V E) (ω : Set E)
    (F : Set E) (hF : F.Finite) (x : V) (hx : (cluster G (ω ∪ F) x).Infinite) :
    ∃ z, Conn G (ω ∪ F) x z ∧ (cluster G ω z).Infinite := by
  by_contra hn
  have hfin (z : V) : (cluster G ω z ∩ cluster G (ω ∪ F) x).Finite := by
    by_cases hz : Conn G (ω ∪ F) x z
    · have hf : (cluster G ω z).Finite := by
        by_contra hh
        exact hn ⟨z,hz,hh⟩
      exact hf.inter_of_left _
    · have he : cluster G ω z ∩ cluster G (ω ∪ F) x = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro y ⟨hzy,hxy⟩
        apply hz
        exact conn_trans G _ hxy (conn_symm G _ (conn_mono G Set.subset_union_left hzy))
      rw [he]
      exact Set.finite_empty
  have hupper : (cluster G ω x ∩ cluster G (ω ∪ F) x ∪
      ⋃ e ∈ F, ⋃ z ∈ {z | z ∈ G e}, cluster G ω z ∩ cluster G (ω ∪ F) x).Finite := by
    apply (hfin x).union
    apply hF.biUnion
    intro e _
    have he : {z | z ∈ G e}.Finite :=
      (G e).toFinset.finite_toSet.subset (fun z hz => by simpa using hz)
    exact he.biUnion (fun z _ => hfin z)
  apply hx (hupper.subset ?_)
  intro y hy
  rcases cluster_union_subset G ω F x hy with hy' | hy'
  · exact Or.inl ⟨hy',hy⟩
  · right
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hy' ⊢
    obtain ⟨e,he,z,hz,hzy⟩ := hy'
    exact ⟨e,he,z,hz,hzy,hy⟩

theorem finite_opening_unique (G : BondGraph V E) (ω : Set E) (F : Finset E) (x : V)
    (hx : (cluster G ω x).Infinite)
    (hjoin : ∀ y, (cluster G ω y).Infinite → Conn G (ω ∪ (F:Set E)) x y) :
    ∃! C, C ∈ infiniteClusters G (ω ∪ (F:Set E)) := by
  rw [unique_infinite_cluster_iff]
  refine ⟨x,hx.mono (fun _ h => conn_mono G Set.subset_union_left h),?_⟩
  intro y hy
  obtain ⟨z,hyz,hz⟩ := infinite_cluster_union_contains G ω (F:Set E) F.finite_toSet y hy
  exact conn_trans G _ (hjoin z hz) (conn_symm G _ hyz)

theorem finite_connecting_edges (G : BondGraph V E) (hconn : Connected G)
    (x : V) (R : Finset V) : ∃ F : Finset E, ∀ y ∈ R, Conn G (F:Set E) x y := by
  have hall (y : V) : ∃ F : Finset E, Conn G (F:Set E) x y := by
    obtain ⟨s,_,hs⟩ := finiteWitness_conn G x y Set.univ (conn_univ_of_connected G hconn x y)
    exact ⟨s,hs⟩
  choose F hF using hall
  refine ⟨R.biUnion F,?_⟩
  intro y hy
  exact conn_mono G (fun e he => Finset.mem_biUnion.mpr ⟨y,hy,he⟩) (hF y)

end Percolation

end OAI
