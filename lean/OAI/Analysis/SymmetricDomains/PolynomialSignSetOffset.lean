import Mathlib
import OAI.Analysis.SymmetricDomains.EventualOffsetBall
import OAI.Analysis.SymmetricDomains.BoundaryFiberClosureContinuity
import OAI.Analysis.SymmetricDomains.PolynomialSignSetVector

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

lemma polynomialSignSet_inwardDistance_graph {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} (A : X → Set (κ → ℝ))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ A z.1}) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = inwardDistance A z.1} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  have ht : PolynomialSignSet d {z | 1 < z.2} := by
    convert PolynomialSignSet.positive (c := d) (MvPolynomial.X none-1) using 1
    ext z
    simp [d]
  have hn := polynomialSignSet_near_fiber A hA (fun _ => 0)
  apply polynomialSignSet_graph_of_sublevel (f := inwardDistance A)
  convert ht.union hn using 1
  ext z
  simp only [mem_ofPred_eq,mem_union]
  by_cases he : (A z.1).Nonempty
  · simp only [inwardDistance,ite_eq_left he,min_lt_iff,infDist_lt_iff he]
    rfl
  · have ha := Set.not_nonempty_iff_eq_empty.mp he
    simp [inwardDistance,ha]

lemma polynomialSignSet_scaled_complement {X ι κ : Type*}
    {c : X → ι → ℝ} (A : X → Set (κ → ℝ))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ A z.1}) :
    PolynomialSignSet
      (fun z : (X × ℝ) × (κ → ℝ) => Sum.elim (fun o => Option.elim o z.1.2 (c z.1.1)) z.2)
      {z | z.2 ∈ (offsetScaled A z.1.1 z.1.2)ᶜ} := by
  exact hA.compl.polynomial_preimage
    (fun z : (X × ℝ) × (κ → ℝ) => (z.1.1,z.1.2 • z.2))
    (Sum.elim (fun i => MvPolynomial.X (Sum.inl (some i)))
      (fun k => MvPolynomial.X (Sum.inl none)*MvPolynomial.X (Sum.inr k))) (by
        intro z i
        cases i <;> simp)

lemma polynomialSignSet_offsetDistance_graph {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} (A : X → Set (κ → ℝ))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ A z.1}) (v : κ → ℝ) :
    PolynomialSignSet (fun z : (X × ℝ) × ℝ => fun o => Option.elim o z.2
      (fun o => Option.elim o z.1.2 (c z.1.1)))
      {z | z.2 = offsetDistance A z.1.1 z.1.2 v} := by
  have hh := polynomialSignSet_infDist_graph
    (c := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
    (fun p : X × ℝ => (offsetScaled A p.1 p.2)ᶜ)
    (polynomialSignSet_scaled_complement A hA) (fun k => MvPolynomial.C (v k))
  have hh' : PolynomialSignSet (fun z : (X × ℝ) × ℝ => fun o => Option.elim o z.2
      (fun o => Option.elim o z.1.2 (c z.1.1)))
      {z | z.2 = infDist v (offsetScaled A z.1.1 z.1.2)ᶜ} := by
    simpa only [MvPolynomial.eval_C] using hh
  exact polynomialSignSet_truncated_graph
    (c := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
    (f := fun z : X × ℝ => infDist v (offsetScaled A z.1 z.2)ᶜ) hh' 1

end Release061.SignElimination

end

end OAI
