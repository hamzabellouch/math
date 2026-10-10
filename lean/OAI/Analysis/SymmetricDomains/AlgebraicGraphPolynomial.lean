import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialEmptyInterior

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
namespace Release061
open Set Filter Topology

theorem real_graph_empty_interior {ι : Type*} [Fintype ι]
    (B : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) :
    interior {x : Option ι → ℝ | (fun i => x (some i)) ∈ B ∧
      x none = f (fun i => x (some i))} = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxS := interior_subset hx
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let y : Option ι → ℝ := x + Pi.single none (r/2)
  have hdist : dist y x < r := by
    rw [dist_eq_norm]
    change ‖x + Pi.single none (r/2) - x‖ < r
    rw [add_sub_cancel_left,Pi.norm_single]
    rw [Real.norm_eq_abs,abs_of_pos (by positivity : 0 < r/2)]
    linarith
  have hyS := hball hdist
  have hyeq := hyS.2
  change y none = _ at hyeq
  simp only [y,Pi.add_apply,Pi.single_eq_same,Pi.single_eq_of_ne (Option.some_ne_none _),add_zero] at hyeq
  linarith [hxS.2,hyeq]

theorem semialgebraic_graph_polynomial {ι : Type*} [Fintype ι]
    (B : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hgraph : PolynomialSignSet (id : (Option ι → ℝ) → (Option ι → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    ∃ P : MvPolynomial (Option ι) ℝ, P ≠ 0 ∧
      ∀ s ∈ B, MvPolynomial.eval (fun a => a.elim (f s) s) P = 0 := by
  obtain ⟨P,hP,hzero⟩ := hgraph.polynomial_of_empty_interior continuous_id
    (real_graph_empty_interior B f)
  exact ⟨P,hP,fun s hs => hzero _ ⟨hs,rfl⟩⟩

theorem algebraic_of_graph_polynomial {R F ι : Type*}
    [Field R] [Field F] [Algebra R F]
    (x : ι → F) (hx : AlgebraicIndependent R x) (y : F)
    (P : MvPolynomial (Option ι) R) (hP : P ≠ 0)
    (hzero : MvPolynomial.aeval (fun a => a.elim y x) P = 0) :
    IsAlgebraic (IntermediateField.adjoin R (range x)) y := by
  let L := IntermediateField.adjoin R (range x)
  let xL : ι → L := fun i => ⟨x i,IntermediateField.subset_adjoin _ _ (mem_range_self i)⟩
  have hxi : Function.Injective (MvPolynomial.aeval xL : MvPolynomial ι R →ₐ[R] L) := by
    apply Function.Injective.of_comp (f := L.val)
    change Function.Injective (L.val ∘ MvPolynomial.aeval xL)
    have heq : L.val.comp (MvPolynomial.aeval xL) = MvPolynomial.aeval x :=
      MvPolynomial.comp_aeval xL L.val
    change Function.Injective (L.val.comp (MvPolynomial.aeval xL))
    rw [heq]
    exact algebraicIndependent_iff_injective_aeval.mp hx
  let Q : Polynomial L := (MvPolynomial.optionEquivLeft R ι P).map (MvPolynomial.aeval xL).toRingHom
  refine ⟨Q,?_,?_⟩
  · have h := (Polynomial.map_injective (MvPolynomial.aeval xL).toRingHom hxi).ne
      ((MvPolynomial.optionEquivLeft R ι).injective.ne hP)
    simpa only [Q, map_zero, Polynomial.map_zero] using h
  · have heval (P : MvPolynomial (Option ι) R) :
        Polynomial.aeval y ((MvPolynomial.optionEquivLeft R ι P).map (MvPolynomial.aeval xL).toRingHom) =
          MvPolynomial.aeval (fun a => a.elim y x) P := by
      induction P using MvPolynomial.induction_on with
      | C c =>
        simp only [MvPolynomial.optionEquivLeft_C,Polynomial.map_C,Polynomial.aeval_C]
        change (algebraMap L F) (MvPolynomial.aeval xL (MvPolynomial.C c)) = _
        rw [MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply, MvPolynomial.aeval_C]
      | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
      | mul_X p i hp =>
        cases i with
        | none => simp only [map_mul,MvPolynomial.optionEquivLeft_X_none,Polynomial.map_mul,
            Polynomial.map_X,Polynomial.aeval_X,MvPolynomial.aeval_X,Option.elim_none,hp]
        | some i =>
          simp only [map_mul,MvPolynomial.optionEquivLeft_X_some,Polynomial.map_mul,
            Polynomial.map_C,Polynomial.aeval_C,MvPolynomial.aeval_X,Option.elim_some,hp]
          change _ * algebraMap L F (MvPolynomial.aeval xL (MvPolynomial.X i)) = _
          rw [MvPolynomial.aeval_X]
          rfl
    exact (heval P).trans hzero

end Release061

end

end OAI
