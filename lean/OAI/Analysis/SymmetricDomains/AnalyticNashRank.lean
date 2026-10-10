import Mathlib
import OAI.Analysis.SymmetricDomains.AlgebraicIndependentNashPartials

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

section
open Set Algebra KaehlerDifferential Module

theorem nash_partial_span_rank_eq_trdeg
    {R F ι κ : Type} [Field R] [CharZero R] [Field F] [Algebra R F]
    [Fintype ι] [DecidableEq ι]
    (x : ι → F) (hx : AlgebraicIndependent R x)
    (δ : ι → Derivation R F F)
    (hδ : ∀ i j, δ i (x j) = if j = i then 1 else 0)
    (q : κ → F) (hqalg : ∀ j, IsAlgebraic (IntermediateField.adjoin R (range x)) (q j)) :
    Module.rank F (Submodule.span F (range (fun j i => δ i (q j)))) =
      Algebra.trdeg R (IntermediateField.adjoin R (range q)) := by
  let Q := Submodule.span F (range (fun j => D R F (q j)))
  let X := Submodule.span F (range (fun i => D R F (x i)))
  let L : Ω[F⁄R] →ₗ[F] (ι → F) := LinearMap.pi fun i => (δ i).liftKaehlerDifferential
  have hQX : Q ≤ X := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact differential_mem_span_of_isAlgebraic_adjoin x hx _ (hqalg j)
  have hinj : Function.Injective (L.comp Q.subtype) := by
    intro a b hab
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply partials_injective_on_differential_span x δ hδ (hQX (Q.sub_mem a.property b.property))
    intro i
    have hi := congrFun hab i
    change (δ i).liftKaehlerDifferential a.val = (δ i).liftKaehlerDifferential b.val at hi
    rw [map_sub,hi,sub_self]
  have heq : LinearMap.range (L.comp Q.subtype) =
      Submodule.span F (range (fun j i => δ i (q j))) := by
    rw [LinearMap.range_comp,Submodule.range_subtype]
    change (Submodule.span F _).map L = _
    rw [Submodule.map_span,← Set.range_comp]
    congr 2
    funext j i
    exact Derivation.liftKaehlerDifferential_comp_D (δ i) (q j)
  rw [← heq,rank_range_of_injective _ hinj]
  exact differential_span_rank_eq_trdeg q

end

open Set Filter Topology

noncomputable def meromorphicGermOf {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : E → ℂ) (hf : AnalyticAt ℂ f 0) : MeromorphicGermField E :=
  algebraMap (AnalyticGerm E) (MeromorphicGermField E) (analyticGermOf E f hf)

@[simp] theorem meromorphicGermOf_eq_zero_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : E → ℂ) (hf : AnalyticAt ℂ f 0) :
    meromorphicGermOf f hf = 0 ↔ f =ᶠ[𝓝 (0:E)] 0 := by
  rw [meromorphicGermOf, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  exact (analyticGermOf_eq_iff E f 0 hf analyticAt_const)

noncomputable def meromorphicPartial {n : ℕ} (i : Fin n) :
    Derivation ℂ (MeromorphicGermField (Fin n → ℂ)) (MeromorphicGermField (Fin n → ℂ)) :=
  meromorphicDirectionalDerivation _ (Pi.single i 1)

@[simp] theorem meromorphicPartial_coordinate {n : ℕ} (i j : Fin n) :
    meromorphicPartial i (meromorphicCoordinate j) = if j = i then 1 else 0 := by
  rw [meromorphicPartial,meromorphicDirectionalDerivation_coordinate]
  by_cases h : j = i
  · subst j; simp
  · simp [h]

theorem meromorphicGerm_aeval_eq_zero_iff {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ι → E → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (P : MvPolynomial ι ℂ) :
    MvPolynomial.aeval (fun i => meromorphicGermOf (f i) (hf i)) P = 0 ↔
      (fun x => MvPolynomial.eval (fun i => f i x) P) =ᶠ[𝓝 (0:E)] 0 := by
  let A := AnalyticGerm E
  let K := MeromorphicGermField E
  have heq : MvPolynomial.aeval (fun i => meromorphicGermOf (f i) (hf i)) P =
      algebraMap A K (MvPolynomial.aeval (fun i => analyticGermOf E (f i) (hf i)) P) := by
    exact (MvPolynomial.comp_aeval_apply (fun i => analyticGermOf E (f i) (hf i)) (IsScalarTower.toAlgHom ℂ A K) P).symm
  rw [heq, map_eq_zero_iff _ (IsFractionRing.injective A K)]
  constructor
  · intro h
    apply Filter.Germ.coe_eq.mp
    rw [← analyticGerm_aeval f hf P]
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    rw [analyticGerm_aeval f hf P]
    exact Filter.Germ.coe_eq.mpr h

theorem analytic_nash_polynomial_relation {n N : ℕ}
    (f : Fin N → (Fin n → ℂ) → ℂ) (hf : ∀ j, AnalyticAt ℂ (f j) 0)
    (halg : ∀ j, IsAlgebraic (IntermediateField.adjoin ℂ
      (range (meromorphicCoordinate (n := n)))) (meromorphicGermOf (f j) (hf j)))
    (hrank : ¬ LinearIndependent (MeromorphicGermField (Fin n → ℂ))
      (fun j i => meromorphicPartial i (meromorphicGermOf (f j) (hf j)))) :
    ∃ P : MvPolynomial (Fin N) ℂ, P ≠ 0 ∧
      (fun x => MvPolynomial.eval (fun j => f j x) P) =ᶠ[𝓝 (0 : Fin n → ℂ)] 0 := by
  classical
  by_contra h
  push Not at h
  apply hrank
  apply algebraicIndependent_nash_partials meromorphicCoordinate
    algebraicIndependent_meromorphicCoordinate meromorphicPartial meromorphicPartial_coordinate
    (fun j => meromorphicGermOf (f j) (hf j)) halg
  rw [algebraicIndependent_iff_ker_eq_bot]
  apply le_antisymm _ bot_le
  intro P hP
  simp only [RingHom.mem_ker,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] at hP
  have hzero : P = 0 := by
    by_contra hne
    exact h P hne ((meromorphicGerm_aeval_eq_zero_iff f hf P).mp hP)
  simpa only [Ideal.mem_bot] using hzero

theorem analytic_nash_rank {n N : ℕ}
    (f : Fin N → (Fin n → ℂ) → ℂ) (hf : ∀ j, AnalyticAt ℂ (f j) 0)
    (halg : ∀ j, IsAlgebraic (IntermediateField.adjoin ℂ
      (range (meromorphicCoordinate (n := n)))) (meromorphicGermOf (f j) (hf j))) :
    Module.rank (MeromorphicGermField (Fin n → ℂ))
      (Submodule.span (MeromorphicGermField (Fin n → ℂ))
        (range (fun j i => meromorphicPartial i (meromorphicGermOf (f j) (hf j))))) =
      Algebra.trdeg ℂ (IntermediateField.adjoin ℂ (range
        (fun j => meromorphicGermOf (f j) (hf j)))) := by
  exact nash_partial_span_rank_eq_trdeg meromorphicCoordinate
    algebraicIndependent_meromorphicCoordinate meromorphicPartial meromorphicPartial_coordinate
    (fun j => meromorphicGermOf (f j) (hf j)) halg

end Release061

end

end OAI
