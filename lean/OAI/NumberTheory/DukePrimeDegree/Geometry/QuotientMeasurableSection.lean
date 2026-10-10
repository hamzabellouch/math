import OAI.NumberTheory.PrimePackets.RootCharts
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.Topology.Bases

namespace OAI

/-! # A measurable section of the actual arithmetic quotient

Local inverse charts and a countable disjoint cover give the section. It
is used to lift an arbitrary quotient measure before taking neutral leaf
coordinates; no absolute continuity with respect to Haar is required.
-/

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_measurable_quotient_section (n : ℕ) :
    ∃ s : X n → G n, Measurable s ∧
      ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x := by
  classical
  let q : G n → X n := Quotient.mk (QuotientGroup.rightRel (integralGroup n))
  have hq := (quotient_covering n).isLocalHomeomorph
  choose e he hqe using hq
  have hcover : (⋃ g : G n, (e g).target)=univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨g,rfl⟩ := Quotient.mk_surjective x
    apply mem_iUnion.mpr
    refine ⟨g,?_⟩
    have h := (e g).map_source (he g)
    rwa [←hqe g] at h
  obtain ⟨S,hSuniv,hSc,hS⟩ := isOpen_biUnion_countable (univ : Set (G n))
    (fun g => (e g).target) (fun g _ => (e g).open_target)
  obtain ⟨a,ha⟩ := Set.countable_iff_exists_subset_range.mp hSc
  have hSall : (⋃ g ∈ S, (e g).target)=univ := hS.trans (by simpa using hcover)
  let U : ℕ → Set (X n) := fun i => (e (a i)).target
  have hU : (⋃ i, U i)=univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ g ∈ S, (e g).target := by
      rw [hSall]
      trivial
    obtain ⟨g,hg,hxg⟩ := mem_iUnion₂.mp hx
    obtain ⟨i,rfl⟩ := ha hg
    exact mem_iUnion.mpr ⟨i,hxg⟩
  let D : ℕ → Set (X n) := disjointed U
  have hD (i : ℕ) : MeasurableSet (D i) :=
    MeasurableSet.disjointed (fun j => (e (a j)).open_target.measurableSet) i
  let f : ℕ → X n → G n := fun i => (U i).piecewise (e (a i)).symm (fun _ => 1)
  have hf (i : ℕ) : Measurable (f i) :=
    (e (a i)).continuousOn_invFun.measurable_piecewise continuous_const.continuousOn
      (e (a i)).open_target.measurableSet
  obtain ⟨s,hs,hsi⟩ := exists_measurable_piecewise D hD f hf (by
    intro i j hij x hx
    exact ((Set.disjoint_left.mp ((disjoint_disjointed U) hij)) hx.1 hx.2).elim)
  refine ⟨s,hs,?_⟩
  intro x
  have hx : x ∈ ⋃ i, D i := by rw [iUnion_disjointed,hU]; trivial
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  have hui : x ∈ U i := disjointed_subset U i hi
  rw [hsi i hi]
  change q ((U i).piecewise (e (a i)).symm (fun _ => 1) x)=x
  rw [piecewise_eq_of_mem _ _ _ hui]
  dsimp only [q]
  rw [hqe (a i)]
  exact (e (a i)).right_inv hui

end DukePrimeDegree

end

end OAI
