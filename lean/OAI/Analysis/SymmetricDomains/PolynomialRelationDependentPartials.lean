import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

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
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin

noncomputable def transcendenceDifferentialBasis
    {R K ι : Type*} [Field R] [CharZero R] [Field K] [Algebra R K]
    (x : ι → K) (hx : IsTranscendenceBasis R x) : Basis ι K Ω[K⁄R] := by
  let P := MvPolynomial ι R
  let A := Algebra.adjoin R (range x)
  let L := IntermediateField.adjoin R (range x)
  let f : P →ₐ[R] L := (IsScalarTower.toAlgHom R A L).comp hx.1.aevalEquiv.toAlgHom
  let : Algebra P L := f.toRingHom.toAlgebra
  let : Algebra P K := (MvPolynomial.aeval x).toRingHom.toAlgebra
  let : IsScalarTower R P L := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  let : IsScalarTower R P K := IsScalarTower.of_algebraMap_eq fun r =>
    (MvPolynomial.aeval x).commutes r |>.symm
  let : IsScalarTower P L K := IsScalarTower.of_algebraMap_eq fun p => rfl
  let : IsFractionRing P L := IsFractionRing.of_ringEquiv_left
    hx.1.aevalEquiv.toRingEquiv (fun _ => rfl)
  let : Algebra.IsAlgebraic L K := hx.isAlgebraic_field
  let : Algebra.FormallyEtale P L :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (nonZeroDivisors P)
  let : Algebra.FormallyEtale L K := Algebra.FormallyEtale.of_isSeparable L K
  let : Algebra.FormallyEtale P K := Algebra.FormallyEtale.comp P L K
  exact ((KaehlerDifferential.mvPolynomialBasis R ι).baseChange K).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R P K)

@[simp]
theorem transcendenceDifferentialBasis_apply
    {R K ι : Type*} [Field R] [CharZero R] [Field K] [Algebra R K]
    (x : ι → K) (hx : IsTranscendenceBasis R x) (i : ι) :
    transcendenceDifferentialBasis x hx i = D R K (x i) := by
  have hpoly : KaehlerDifferential.mvPolynomialBasis R ι i =
      D R (MvPolynomial ι R) (MvPolynomial.X i) := by
    apply (KaehlerDifferential.mvPolynomialBasis R ι).repr.injective
    simp
  simp only [transcendenceDifferentialBasis,Basis.map_apply,Basis.baseChange_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul,one_smul,hpoly,KaehlerDifferential.map_D]
  change D R K ((MvPolynomial.aeval x) (MvPolynomial.X i)) = _
  simp

theorem algebraicIndependent_differentials
    {R K ι : Type*} [Field R] [CharZero R] [Field K] [Algebra R K]
    (x : ι → K) (hx : AlgebraicIndependent R x) :
    LinearIndependent K (fun i => D R K (x i)) := by
  obtain ⟨s,hxs,hs⟩ := exists_isTranscendenceBasis_superset
    ((algebraicIndependent_subtype_range hx.injective).2 hx)
  let q : ι → s := fun i => ⟨x i,hxs (mem_range_self i)⟩
  have hq : Function.Injective q := by
    intro i j hij
    exact hx.injective (congrArg Subtype.val hij)
  have hlin := (transcendenceDifferentialBasis (fun z : s => z.val) hs).linearIndependent.comp q hq
  simpa only [Function.comp_def,transcendenceDifferentialBasis_apply,q] using hlin

end

open Set Algebra KaehlerDifferential Module

theorem derivation_transcendence_coordinates
    {R K ι : Type*} [Field R] [CharZero R] [Field K] [Algebra R K]
    [Finite ι] [DecidableEq ι]
    (x : ι → K) (hx : IsTranscendenceBasis R x)
    (δ : ι → Derivation R K K)
    (hδ : ∀ i j, δ i (x j) = if j = i then 1 else 0) (y : K) (i : ι) :
    δ i y = (transcendenceDifferentialBasis x hx).equivFun (D R K y) i := by
  have heq : (δ i).liftKaehlerDifferential =
      (LinearMap.proj i).comp (transcendenceDifferentialBasis x hx).equivFun.toLinearMap := by
    apply (transcendenceDifferentialBasis x hx).ext
    intro j
    change (δ i).liftKaehlerDifferential ((transcendenceDifferentialBasis x hx) j) =
      (transcendenceDifferentialBasis x hx).equivFun ((transcendenceDifferentialBasis x hx) j) i
    rw [Basis.equivFun_self, transcendenceDifferentialBasis_apply,
      Derivation.liftKaehlerDifferential_comp_D]
    exact hδ i j
  simpa only [Derivation.liftKaehlerDifferential_comp_D, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearEquiv.coe_coe] using congrArg (fun L => L (D R K y)) heq

theorem algebraicIndependent_partialDerivatives
    {R K ι κ : Type*} [Field R] [CharZero R] [Field K] [Algebra R K]
    [Finite ι] [DecidableEq ι]
    (x : ι → K) (hx : IsTranscendenceBasis R x)
    (δ : ι → Derivation R K K)
    (hδ : ∀ i j, δ i (x j) = if j = i then 1 else 0)
    (q : κ → K) (hq : AlgebraicIndependent R q) :
    LinearIndependent K (fun j i => δ i (q j)) := by
  have H := (algebraicIndependent_differentials q hq).map'
    (transcendenceDifferentialBasis x hx).equivFun.toLinearMap
    (LinearMap.ker_eq_bot.mpr (transcendenceDifferentialBasis x hx).equivFun.injective)
  have heq : (fun j i => δ i (q j)) =
      (fun j => (transcendenceDifferentialBasis x hx).equivFun (D R K (q j))) := by
    funext j i
    exact derivation_transcendence_coordinates x hx δ hδ (q j) i
  rw [heq]
  exact H

theorem polynomial_relation_of_dependent_partials
    {R K ι κ : Type*} [Field R] [CharZero R] [Field K] [Algebra R K]
    [Finite ι] [DecidableEq ι]
    (x : ι → K) (hx : IsTranscendenceBasis R x)
    (δ : ι → Derivation R K K)
    (hδ : ∀ i j, δ i (x j) = if j = i then 1 else 0)
    (q : κ → K) (hq : ¬ LinearIndependent K (fun j i => δ i (q j))) :
    ∃ P : MvPolynomial κ R, P ≠ 0 ∧ MvPolynomial.aeval q P = 0 := by
  classical
  by_contra h
  push Not at h
  apply hq
  apply algebraicIndependent_partialDerivatives x hx δ hδ q
  rw [algebraicIndependent_iff_ker_eq_bot]
  apply le_antisymm _ bot_le
  intro P hP
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hP
  have hzero : P = 0 := by
    by_contra hne
    exact h P hne hP
  simpa only [Ideal.mem_bot] using hzero

end Release061

end

end OAI
