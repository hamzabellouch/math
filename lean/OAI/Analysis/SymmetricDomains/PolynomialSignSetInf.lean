import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialSignSetFinite2

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
namespace Release061.PolynomialSignSet
open Set
open scoped Classical

lemma iff_set {X ι : Type*} {c : X → ι → ℝ} {P Q : X → Prop}
    (hP : PolynomialSignSet c {x | P x}) (hQ : PolynomialSignSet c {x | Q x}) :
    PolynomialSignSet c {x | P x ↔ Q x} := by
  convert (hP.inter hQ).union (hP.compl.inter hQ.compl) using 1
  ext x
  simp only [mem_ofPred_eq,mem_union,mem_inter_iff,mem_compl_iff]
  tauto

lemma norm_lt_polynomial {X ι κ : Type*} [Fintype κ] {c : X → ι → ℝ}
    (p : κ → MvPolynomial ι ℝ) (q : MvPolynomial ι ℝ) :
    PolynomialSignSet c {x | ‖fun k => MvPolynomial.eval (c x) (p k)‖ <
      MvPolynomial.eval (c x) q} := by
  have h := (PolynomialSignSet.positive (c := c) q).inter
    (PolynomialSignSet.forall_finite (fun k x =>
      0 < MvPolynomial.eval (c x) (q+p k) ∧ 0 < MvPolynomial.eval (c x) (q-p k))
      (fun k => (PolynomialSignSet.positive (q+p k)).inter
        (PolynomialSignSet.positive (q-p k))))
  convert h using 1
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq,MvPolynomial.eval_add,MvPolynomial.eval_sub]
  constructor
  · intro hx
    have hq : 0 < MvPolynomial.eval (c x) q := (norm_nonneg _).trans_lt hx
    refine ⟨hq,fun k => ?_⟩
    have hk := (pi_norm_lt_iff hq).mp hx k
    rw [Real.norm_eq_abs,abs_lt] at hk
    constructor <;> linarith [hk.1,hk.2]
  · rintro ⟨hq,h⟩
    apply (pi_norm_lt_iff hq).mpr
    intro k
    rw [Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [(h k).1,(h k).2]

end Release061.PolynomialSignSet

namespace Release061.SignElimination
open Set Metric
open scoped Classical

lemma polynomialSignSet_forall_one {X ι : Type*} {c : X → ι → ℝ}
    {P : X × ℝ → Prop}
    (h : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | P z}) : PolynomialSignSet c {x | ∀ t : ℝ, P (x,t)} := by
  convert (polynomialSignSet_projection_one h.compl).compl using 1
  ext x
  simp

lemma polynomialSignSet_graph_of_sublevel {X ι : Type*} {c : X → ι → ℝ}
    {f : X → ℝ}
    (h : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | f z.1 < z.2}) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = f z.1} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  let e := fun z : (X × ℝ) × ℝ => fun o => Option.elim o z.2 (d z.1)
  have hh : PolynomialSignSet e {z | f z.1.1 < z.2} :=
    h.coordinate_preimage (fun z : (X × ℝ) × ℝ => (z.1.1,z.2))
      (fun o => Option.elim o none (fun i => some (some i))) (by
        intro z o; cases o <;> rfl)
  have ht : PolynomialSignSet e {z | z.1.2 < z.2} := by
    convert PolynomialSignSet.positive (c := e)
      (MvPolynomial.X none-MvPolynomial.X (some none)) using 1
    ext z
    simp [e,d]
  have hq := polynomialSignSet_forall_one (hh.iff_set ht)
  convert hq using 1
  ext z
  simp only [mem_ofPred_eq]
  constructor
  · intro hz t
    rw [hz]
  · intro hz
    exact le_antisymm (le_of_not_gt (fun hlt => (lt_irrefl _) ((hz z.2).mp hlt)))
      (le_of_not_gt (fun hlt => (lt_irrefl _) ((hz (f z.1)).mpr hlt)))

lemma polynomialSignSet_near_fiber {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} (A : X → Set (κ → ℝ))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ A z.1}) (p : κ → MvPolynomial ι ℝ) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | ∃ y ∈ A z.1, dist (fun k => MvPolynomial.eval (c z.1) (p k)) y < z.2} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  let e := fun z : (X × ℝ) × (κ → ℝ) => Sum.elim (d z.1) z.2
  have ha : PolynomialSignSet e {z | z.2 ∈ A z.1.1} :=
    hA.coordinate_preimage (fun z : (X × ℝ) × (κ → ℝ) => (z.1.1,z.2)) (Sum.map some id)
      (by intro z i; cases i <;> rfl)
  have hn : PolynomialSignSet e {z | dist
      (fun k => MvPolynomial.eval (c z.1.1) (p k)) z.2 < z.1.2} := by
    convert PolynomialSignSet.norm_lt_polynomial (c := e)
      (fun k => MvPolynomial.rename (fun i => Sum.inl (some i)) (p k)-MvPolynomial.X (Sum.inr k))
      (MvPolynomial.X (Sum.inl none)) using 1
    ext z
    simp only [mem_ofPred_eq,dist_eq_norm,MvPolynomial.eval_sub,MvPolynomial.eval_X,
      MvPolynomial.eval_rename]
    rfl
  exact polynomialSignSet_projection_finite (ha.inter hn)

lemma polynomialSignSet_infDist_graph {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} (A : X → Set (κ → ℝ))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ A z.1}) (p : κ → MvPolynomial ι ℝ) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = infDist (fun k => MvPolynomial.eval (c z.1) (p k)) (A z.1)} := by
  have hne : PolynomialSignSet c {x | (A x).Nonempty} :=
    polynomialSignSet_projection_finite hA
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  have hemp : PolynomialSignSet d {z | ¬ (A z.1).Nonempty} :=
    hne.compl.coordinate_preimage Prod.fst some (by intros; rfl)
  have ht : PolynomialSignSet d {z | 0 < z.2} := by
    simpa only [MvPolynomial.eval_X,d,Option.elim_none] using
      (PolynomialSignSet.positive (c := d) (MvPolynomial.X none))
  have hsub := (hemp.inter ht).union (polynomialSignSet_near_fiber A hA p)
  apply polynomialSignSet_graph_of_sublevel (f := fun x => infDist (fun k => MvPolynomial.eval (c x) (p k)) (A x))
  convert hsub using 1
  ext z
  simp only [mem_ofPred_eq,mem_union,mem_inter_iff]
  by_cases he : (A z.1).Nonempty
  · simp only [he,not_true_eq_false,false_and,false_or,infDist_lt_iff he]
  · have ha := Set.not_nonempty_iff_eq_empty.mp he
    simp [ha]

end Release061.SignElimination

end

end OAI
