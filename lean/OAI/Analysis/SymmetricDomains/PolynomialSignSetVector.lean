import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialSignSetInf

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
namespace Release061.SignElimination
open Set Metric
open scoped Classical

lemma polynomialSignSet_sublevel_of_graph {X ι : Type*} {c : X → ι → ℝ}
    {f : X → ℝ}
    (h : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = f z.1}) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | f z.1 < z.2} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  let e := fun z : (X × ℝ) × ℝ => fun o => Option.elim o z.2 (d z.1)
  have hh : PolynomialSignSet e {z | z.2 = f z.1.1} :=
    h.coordinate_preimage (fun z : (X × ℝ) × ℝ => (z.1.1,z.2))
      (fun o => Option.elim o none (fun i => some (some i))) (by
        intro z o; cases o <;> rfl)
  have ht : PolynomialSignSet e {z | z.2 < z.1.2} := by
    convert PolynomialSignSet.positive (c := e)
      (MvPolynomial.X (some none)-MvPolynomial.X none) using 1
    ext z
    simp [e,d]
  convert polynomialSignSet_projection_one (hh.inter ht) using 1
  ext z
  simp

lemma polynomialSignSet_truncated_graph {X ι : Type*} {c : X → ι → ℝ}
    {f : X → ℝ}
    (h : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = f z.1}) (a : ℝ) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = min a (f z.1)} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  have ht : PolynomialSignSet d {z | a < z.2} := by
    convert PolynomialSignSet.positive (c := d) (MvPolynomial.X none-MvPolynomial.C a) using 1
    ext z
    simp [d]
  apply polynomialSignSet_graph_of_sublevel (f := fun x => min a (f x))
  convert ht.union (polynomialSignSet_sublevel_of_graph h) using 1
  ext z
  simp only [mem_ofPred_eq,mem_union,min_lt_iff]

lemma polynomialSignSet_vector_graph_coordinate {X ι κ : Type*} [Finite κ]
    {c : X → ι → ℝ} {S : Set X} {f : X → κ → ℝ}
    (h : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.1 ∈ S ∧ z.2 = f z.1}) (j : κ) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.1 ∈ S ∧ z.2 = f z.1 j} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  let e := fun z : (X × ℝ) × (κ → ℝ) => Sum.elim (d z.1) z.2
  have hh : PolynomialSignSet e {z | z.1.1 ∈ S ∧ z.2 = f z.1.1} :=
    h.coordinate_preimage (fun z : (X × ℝ) × (κ → ℝ) => (z.1.1,z.2)) (Sum.map some id)
      (by intro z i; cases i <;> rfl)
  have he : PolynomialSignSet e {z | z.1.2 = z.2 j} := by
    convert PolynomialSignSet.zero (c := e)
      (MvPolynomial.X (Sum.inl none)-MvPolynomial.X (Sum.inr j)) using 1
    ext z
    simp [e,d,sub_eq_zero]
  convert polynomialSignSet_projection_finite (hh.inter he) using 1
  ext z
  simp only [mem_ofPred_eq,mem_inter_iff]
  constructor
  · rintro ⟨hs,ht⟩
    exact ⟨f z.1,⟨hs,rfl⟩,ht⟩
  · rintro ⟨y,⟨hs,rfl⟩,ht⟩
    exact ⟨hs,ht⟩

end Release061.SignElimination

end

end OAI
