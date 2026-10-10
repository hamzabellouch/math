import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticNashRefinement

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

namespace PolynomialSignSet
variable {X ι : Type*} {c : X → ι → ℝ} {P Q : X → Prop}
lemma iff (hP : PolynomialSignSet c {x | P x}) (hQ : PolynomialSignSet c {x | Q x}) :
    PolynomialSignSet c {x | P x ↔ Q x} := by
  convert (hP.inter hQ).union (hP.compl.inter hQ.compl) using 1
  ext x
  simp only [mem_ofPred_eq,mem_union,mem_inter_iff,mem_compl_iff]
  tauto
lemma implies (hP : PolynomialSignSet c {x | P x}) (hQ : PolynomialSignSet c {x | Q x}) :
    PolynomialSignSet c {x | P x → Q x} := by
  convert hP.compl.union hQ using 1
  ext x
  simp only [mem_ofPred_eq,mem_union,mem_compl_iff]
  tauto
end PolynomialSignSet

def SortedFiber {X : Type*} (R : Set (X × ℝ)) (r : ℕ) : Set (X × (Fin r → ℝ)) :=
  {z | StrictMono z.2 ∧ ∀ y : ℝ, (z.1,y) ∈ R ↔ ∃ i, y = z.2 i}

lemma sortedFiber_unique {X : Type*} {R : Set (X × ℝ)} {r : ℕ} {x : X}
    {u v : Fin r → ℝ} (hu : (x,u) ∈ SortedFiber R r) (hv : (x,v) ∈ SortedFiber R r) : u = v := by
  apply (hu.1.range_inj_of_wellFoundedLT hv.1).mp
  ext y
  simp only [mem_range]
  simpa only [eq_comm] using (hu.2 y).symm.trans (hv.2 y)

lemma sortedFiber_exists {X : Type*} {R : Set (X × ℝ)} {x : X}
    (hfin : {y : ℝ | (x,y) ∈ R}.Finite) :
    ∃ u : Fin hfin.toFinset.card → ℝ, (x,u) ∈ SortedFiber R hfin.toFinset.card := by
  refine ⟨hfin.toFinset.orderEmbOfFin rfl,(hfin.toFinset.orderEmbOfFin rfl).strictMono,?_⟩
  intro y
  have he := Set.ext_iff.mp (Finset.range_orderEmbOfFin hfin.toFinset rfl) y
  simpa only [mem_range,Finset.mem_coe,Set.Finite.mem_toFinset,mem_ofPred_eq,eq_comm] using he.symm

lemma sortedFiber_polynomialSignSet {X ι : Type*} {c : X → ι → ℝ}
    {R : Set (X × ℝ)}
    (hR : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) R) (r : ℕ) :
    PolynomialSignSet (fun z : X × (Fin r → ℝ) => Sum.elim (c z.1) z.2) (SortedFiber R r) := by
  let d := fun z : X × (Fin r → ℝ) => Sum.elim (c z.1) z.2
  have hm : PolynomialSignSet d {z | StrictMono z.2} := by
    apply PolynomialSignSet.forall_finite
    intro i
    apply PolynomialSignSet.forall_finite
    intro j
    apply (PolynomialSignSet.const (c := d) (i < j)).implies
    convert PolynomialSignSet.positive (c := d)
      (MvPolynomial.X (Sum.inr j) - MvPolynomial.X (Sum.inr i)) using 1
    ext z
    simp [d,sub_pos]
  let e := fun z : (X × (Fin r → ℝ)) × ℝ => fun o => Option.elim o z.2 (d z.1)
  have hr : PolynomialSignSet e {z | (z.1.1,z.2) ∈ R} :=
    hR.coordinate_preimage (fun z => (z.1.1,z.2)) (Option.map Sum.inl)
      (d := e) (by intro z o; cases o <;> rfl)
  have he : PolynomialSignSet e {z | ∃ i : Fin r, z.2 = z.1.2 i} := by
    apply PolynomialSignSet.exists_finite
    intro i
    convert PolynomialSignSet.zero (c := e)
      (MvPolynomial.X none - MvPolynomial.X (some (Sum.inr i))) using 1
    ext z
    simp [e,d,sub_eq_zero]
  exact hm.inter (SignElimination.polynomialSignSet_forall_one (hr.iff he))

theorem sorted_fiber_selection {n : ℕ} {R : Set ((Fin n → ℝ) × ℝ)}
    (hR : PolynomialSignSet (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) R)
    (r : ℕ) :
    ∃ B : Set (Fin n → ℝ), ∃ f : (Fin n → ℝ) → (Fin r → ℝ),
      PolynomialSignSet id B ∧ SemialgebraicOn B f ∧
      (∀ x, x ∈ B ↔ ∃ v, (x,v) ∈ SortedFiber R r) ∧
      ∀ x ∈ B, (x,f x) ∈ SortedFiber R r := by
  have hs := sortedFiber_polynomialSignSet (c := id) hR r
  obtain ⟨f,hf,hsf⟩ := SignElimination.polynomialSignSet_choice_finite hs
  refine ⟨{x | ∃ v, (x,v) ∈ SortedFiber R r},f,?_,hsf,fun _ => Iff.rfl,?_⟩
  · exact SignElimination.polynomialSignSet_projection_finite hs
  · exact hf
end Release061

end

end OAI
