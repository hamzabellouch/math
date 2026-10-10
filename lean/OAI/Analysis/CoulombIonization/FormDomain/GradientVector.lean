import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.InsertTest
import OAI.Analysis.CoulombIonization.Localization.FermionGradient

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombSobolev CoulombPackets

def gradientVector {N : ℕ} (ψ : FormVector N) (i : Fin N) (a : Fin 3) : FormVector N where
  value s := ψ.gradient s i a
  gradient _ _ _ _ := 0

def gradientMany {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (i : Fin N) (a : Fin 3) : Many N :=
  toMany (gradientVector ψ i a) (fun s => hψ.2.1 s i a)

lemma weak_test_identity {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (i : Fin N) (a : Fin 3) (φ : Test (Configuration N)) (s : Spins N) :
    inner ℂ (manyTest (φ.deriv (direction i a)) s) (toMany ψ hψ.1) +
      inner ℂ (manyTest φ s) (gradientMany ψ hψ i a) = 0 := by
  have h2 : inner ℂ (manyTest φ s) (gradientMany ψ hψ i a) =
      ∫ x, ψ.gradient s i a x * (φ.fn x : ℂ) :=
    manyTest_inner (gradientVector ψ i a) (fun s => hψ.2.1 s i a) φ s
  rw [manyTest_inner, h2]
  have hw := hψ.2.2.1 s i a φ.fn φ.smooth φ.compact
  have he : (∫ x, ψ.value s x * ((φ.deriv (direction i a)).fn x : ℂ)) =
      ∫ x, ψ.value s x * Complex.ofReal (lineDeriv ℝ φ.fn x (direction i a)) := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [(φ.smooth.differentiable (by simp) x).lineDeriv_eq_fderiv]
    rfl
  rw [he,hw]
  simp

lemma form_hasFermionGradient {N : ℕ} (ψ : FormVector (N+1)) (hψ : FormAdmissible ψ) :
    HasFermionGradient (EuclideanSpace.basisFun (Fin 3) ℝ) (toMany ψ hψ.1)
      (gradientMany ψ hψ) := by
  intro i a φ s
  apply manyTest_total
  intro η τ
  rw [inner_add_right]
  change inner ℂ (manyTest η τ)
      ((tensorLeft (tensor (φ.deriv ((EuclideanSpace.basisFun (Fin 3) ℝ) a)).toL2 (countVector s))).adjoint
        (splitFermion i (toMany ψ hψ.1))) +
    inner ℂ (manyTest η τ) ((tensorLeft (tensor φ.toL2 (countVector s))).adjoint
        (splitFermion i (gradientMany ψ hψ i a))) = 0
  rw [← insert_adjoint_split, ← insert_adjoint_split,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    insertOrbital_manyTest, insertOrbital_manyTest]
  rw [EuclideanSpace.basisFun_apply, ← insertTest_deriv]
  exact weak_test_identity ψ hψ i a (insertTest i φ η) (Fin.insertNth i s τ)

lemma gradientMany_norm_sq {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (i : Fin N) (a : Fin 3) :
    ‖gradientMany ψ hψ i a‖^2 = ∑ s : Spins N, ∫ x, ‖ψ.gradient s i a x‖^2 := by
  exact toMany_norm_sq (gradientVector ψ i a) (fun s => hψ.2.1 s i a)

end CoulombAtom.Pauli

end

end OAI
