import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.ManyTest
import OAI.Analysis.CoulombIonization.FormDomain.CompCL

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
open CoulombPauli CoulombSobolev

lemma coordinateSplit_direction {N : ℕ} (i : Fin (N+1)) (a : Fin 3) :
    coordinateSplit i (direction i a) = (EuclideanSpace.single a 1, 0) := by
  rw [coordinateSplit_apply]
  apply Prod.ext
  · simp [direction]
  · funext j
    simp [direction, Fin.succAbove_ne]

def insertTest {N : ℕ} (i : Fin (N+1)) (φ : Test Space) (η : Test (Configuration N)) :
    Test (Configuration (N+1)) := (φ.tensor η).compCL (coordinateSplit i)

lemma insertTest_deriv {N : ℕ} (i : Fin (N+1)) (a : Fin 3)
    (φ : Test Space) (η : Test (Configuration N)) :
    (insertTest i φ η).deriv (direction i a) =
      insertTest i (φ.deriv (EuclideanSpace.single a 1)) η := by
  rw [insertTest, Test.compCL_deriv, coordinateSplit_direction, Test.tensor_deriv]
  rfl

lemma insertTest_apply {N : ℕ} (i : Fin (N+1)) (φ : Test Space) (η : Test (Configuration N))
    (x : Configuration (N+1)) :
    (insertTest i φ η).fn x = φ.fn (x i) * η.fn (fun j => x (i.succAbove j)) := rfl

lemma insertOrbital_ae {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 oneMeasure) (ψ : Many N) :
    CoulombPauli.insertOrbital i u ψ =ᵐ[configMeasure (N+1) oneMeasure]
      (fun x : Fin (N+1) → OneParticle => u (x i) * ψ (fun j => x (i.succAbove j))) := by
  dsimp only [CoulombPauli.insertOrbital, ContinuousLinearMap.comp_apply, tensorLeft_apply]
  exact (pull_ae _ _ _).trans ((splitAt_preserving i).quasiMeasurePreserving.ae (tensor_ae u ψ))

lemma oneTest_ae (φ : Test Space) (s : Fin 2) :
    tensor φ.toL2 (countVector s) =ᵐ[oneMeasure]
      (fun x : OneParticle => (φ.fn x.1 : ℂ) * (if x.2 = s then 1 else 0)) := by
  filter_upwards [tensor_ae φ.toL2 (countVector s),
    Measure.quasiMeasurePreserving_fst.ae φ.coe_toL2,
    Measure.quasiMeasurePreserving_snd.ae (countVector_ae s)] with x h1 h2 h3
  rw [h1,h2,h3]
  by_cases h : x.2 = s <;> simp [h]

lemma insertOrbital_manyTest {N : ℕ} (i : Fin (N+1)) (φ : Test Space) (η : Test (Configuration N))
    (s : Fin 2) (τ : Spins N) :
    CoulombPauli.insertOrbital i (tensor φ.toL2 (countVector s)) (manyTest η τ) =
      manyTest (insertTest i φ η) (Fin.insertNth i s τ) := by
  apply Lp.ext
  have h1 := (splitAt_preserving i).quasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_fst.ae (oneTest_ae φ s))
  have h2 := (splitAt_preserving i).quasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_snd.ae (manyTest_ae η τ))
  filter_upwards [insertOrbital_ae i (tensor φ.toL2 (countVector s)) (manyTest η τ),
    manyTest_ae (insertTest i φ η) (Fin.insertNth i s τ), h1, h2] with x hx hy hφ hη
  rw [hx,hy]
  change (tensor φ.toL2 (countVector s)) (x i) =
    (φ.fn (x i).1 : ℂ) * (if (x i).2 = s then 1 else 0) at hφ
  change manyTest η τ (fun j => x (i.succAbove j)) =
    (η.fn (fun j => (x (i.succAbove j)).1) : ℂ) *
      (if (fun j => (x (i.succAbove j)).2) = τ then 1 else 0) at hη
  rw [hφ,hη,insertTest_apply, Complex.ofReal_mul]
  have he : ((fun j => (x j).2) = Fin.insertNth i s τ) ↔
      (x i).2 = s ∧ (fun j => (x (i.succAbove j)).2) = τ := Fin.eq_insertNth_iff
  by_cases hs : (x i).2 = s <;> by_cases ht : (fun j => (x (i.succAbove j)).2) = τ <;>
    simp [he, hs, ht]
end CoulombAtom.Pauli

end

end OAI
