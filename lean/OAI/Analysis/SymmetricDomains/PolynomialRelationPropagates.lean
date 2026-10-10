import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticNashRank

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
open Set Filter Topology Algebra

theorem new_polynomial_relation_of_trdeg_lt {R F κ : Type}
    [Field R] [Field F] [Algebra R F]
    (I : Ideal (MvPolynomial κ R)) (q : κ → F)
    (hIq : ∀ P ∈ I, MvPolynomial.aeval q P = 0)
    (hlt : Algebra.trdeg R (IntermediateField.adjoin R (range q)) <
      Algebra.trdeg R (MvPolynomial κ R ⧸ I)) :
    ∃ P : MvPolynomial κ R, P ∉ I ∧ MvPolynomial.aeval q P = 0 := by
  classical
  by_contra hn
  push Not at hn
  let L := IntermediateField.adjoin R (range q)
  let qL : κ → L := fun j => ⟨q j,IntermediateField.subset_adjoin _ _ (mem_range_self j)⟩
  have heval (P : MvPolynomial κ R) : (MvPolynomial.aeval qL P : F) = MvPolynomial.aeval q P := by
    exact MvPolynomial.comp_aeval_apply qL L.val P
  let g : (MvPolynomial κ R ⧸ I) →ₐ[R] L := Ideal.Quotient.liftₐ I
    (MvPolynomial.aeval qL) (fun P hP => by
      apply Subtype.ext
      simpa only [heval,ZeroMemClass.coe_zero] using hIq P hP)
  have hginj : Function.Injective g := by
    apply (injective_iff_map_eq_zero g).mpr
    intro a ha
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mkₐ_surjective R I a
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    by_contra hP
    apply hn P hP
    have hval := congrArg (fun a : L => (a : F)) ha
    change (MvPolynomial.aeval qL P : F) = 0 at hval
    rwa [heval] at hval
  exact (not_le_of_gt hlt) (trdeg_le_of_injective g hginj)

theorem analytic_nash_proper_relation {n N : ℕ}
    (V : Set (Fin N → ℂ))
    (f : Fin N → (Fin n → ℂ) → ℂ) (hf : ∀ j, AnalyticAt ℂ (f j) 0)
    (hfV : ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), (fun j => f j x) ∈ V)
    (halg : ∀ j, IsAlgebraic (IntermediateField.adjoin ℂ
      (range (meromorphicCoordinate (n := n)))) (meromorphicGermOf (f j) (hf j)))
    (hlt : Module.rank (MeromorphicGermField (Fin n → ℂ))
      (Submodule.span (MeromorphicGermField (Fin n → ℂ))
        (range (fun j i => meromorphicPartial i (meromorphicGermOf (f j) (hf j))))) <
      Algebra.trdeg ℂ (MvPolynomial (Fin N) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ V)) :
    ∃ P : MvPolynomial (Fin N) ℂ, (∃ y ∈ V, MvPolynomial.eval y P ≠ 0) ∧
      (fun x => MvPolynomial.eval (fun j => f j x) P) =ᶠ[𝓝 (0 : Fin n → ℂ)] 0 := by
  have hIq : ∀ P ∈ MvPolynomial.vanishingIdeal ℂ V,
      MvPolynomial.aeval (fun j => meromorphicGermOf (f j) (hf j)) P = 0 := by
    intro P hP
    apply (meromorphicGerm_aeval_eq_zero_iff f hf P).mpr
    filter_upwards [hfV] with x hx
    exact MvPolynomial.mem_vanishingIdeal_iff.mp hP _ hx
  rw [analytic_nash_rank f hf halg] at hlt
  obtain ⟨P,hP,hzero⟩ := new_polynomial_relation_of_trdeg_lt
    (MvPolynomial.vanishingIdeal ℂ V) (fun j => meromorphicGermOf (f j) (hf j)) hIq hlt
  refine ⟨P,?_,(meromorphicGerm_aeval_eq_zero_iff f hf P).mp hzero⟩
  simpa only [MvPolynomial.mem_vanishingIdeal_iff,not_forall,exists_prop,MvPolynomial.aeval_eq_eval] using hP

theorem polynomial_relation_propagates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : ℕ} {B : Set E} (hB : IsPreconnected B)
    (q : E → Fin N → ℂ) (hq : AnalyticOnNhd ℝ q B)
    (P : MvPolynomial (Fin N) ℂ) {x : E} (hx : x ∈ B)
    (hzero : (fun y => MvPolynomial.eval (q y) P) =ᶠ[𝓝 x] 0) :
    ∀ y ∈ B, MvPolynomial.eval (q y) P = 0 := by
  have hA : AnalyticOnNhd ℝ (fun y => MvPolynomial.eval (q y) P) B := by
    intro y hy
    exact (((AnalyticOnNhd.eval_mvPolynomial P) (q y) (mem_univ _)).restrictScalars (𝕜 := ℝ)).comp (hq y hy)
  exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hB hx hzero

end Release061

end

end OAI
