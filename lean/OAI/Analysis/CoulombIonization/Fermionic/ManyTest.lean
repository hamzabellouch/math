import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Spin

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

def manyTest {N : ℕ} (φ : Test (Configuration N)) (s : Spins N) : Many N :=
  pull (splitSpin N) (splitSpin_preserving N) (tensor φ.toL2 (countVector s))

lemma manyTest_ae {N : ℕ} (φ : Test (Configuration N)) (s : Spins N) :
    manyTest φ s =ᵐ[configMeasure N oneMeasure] (fun x : Fin N → OneParticle =>
      (φ.fn (fun i => (x i).1) : ℂ) * (if (fun i => (x i).2) = s then 1 else 0)) := by
  have hh : tensor φ.toL2 (countVector s) =ᵐ[volume.prod Measure.count]
      (fun p : Configuration N × Spins N => (φ.fn p.1 : ℂ) * (if p.2 = s then 1 else 0)) := by
    filter_upwards [tensor_ae φ.toL2 (countVector s),
      Measure.quasiMeasurePreserving_fst.ae φ.coe_toL2,
      Measure.quasiMeasurePreserving_snd.ae (countVector_ae s)] with p h1 h2 h3
    rw [h1,h2,h3]
    by_cases h : p.2 = s <;> simp [h]
  exact (pull_ae _ _ _).trans ((splitSpin_preserving N).quasiMeasurePreserving.ae hh)

lemma toMany_eq_pull {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2) :
    toMany ψ hψ = pull (splitSpin N) (splitSpin_preserving N)
      ((memLp_spin ψ.value hψ).toLp _) := by
  apply Lp.ext
  exact (toMany_ae ψ hψ).trans ((pull_ae _ _ _).trans
    ((splitSpin_preserving N).quasiMeasurePreserving.ae (memLp_spin ψ.value hψ).coeFn_toLp)).symm

lemma manyTest_inner {N : ℕ} (ψ : FormVector N) (hψ : ∀ s, MemLp (ψ.value s) 2)
    (φ : Test (Configuration N)) (s : Spins N) :
    inner ℂ (manyTest φ s) (toMany ψ hψ) = ∫ x, ψ.value s x * (φ.fn x : ℂ) := by
  rw [manyTest, toMany_eq_pull, pull_inner]
  exact spin_test_inner ψ.value hψ φ s

lemma manyTest_total {N : ℕ} (ψ : Many N)
    (hψ : ∀ (φ : Test (Configuration N)) (s : Spins N), inner ℂ (manyTest φ s) ψ = 0) : ψ = 0 := by
  let e := splitSpin N
  let he := splitSpin_preserving N
  have hz : pull e.symm (he.symm e) ψ = 0 := by
    apply spin_test_total
    intro φ s
    have hh := hψ φ s
    unfold manyTest at hh
    rw [← pull_symm e he ψ] at hh
    rw [pull_inner] at hh
    exact hh
  have hh := congrArg (pull e he) hz
  simpa only [pull_symm, map_zero] using hh

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
def coordinateSplit {N : ℕ} (i : Fin (N+1)) : (Fin (N+1) → X) ≃L[ℝ] X × (Fin N → X) :=
  ({ toEquiv := (Fin.insertNthEquiv (fun _ : Fin (N+1) => X) i).symm
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : (Fin (N+1) → X) ≃ₗ[ℝ] X × (Fin N → X)).toContinuousLinearEquiv

lemma coordinateSplit_apply {N : ℕ} (i : Fin (N+1)) (x : Fin (N+1) → X) :
    coordinateSplit i x = (x i, fun j => x (i.succAbove j)) := rfl

lemma coordinateSplit_symm_apply {N : ℕ} (i : Fin (N+1)) (z : X × (Fin N → X)) :
    (coordinateSplit i).symm z = Fin.insertNth i z.1 z.2 := rfl

lemma coordinateTest {N : ℕ} (i : Fin (N+1)) (φ : Test Space) (η : Test (Configuration N)) :
    HasCompactSupport (fun x : Configuration (N+1) => φ.fn (x i) * η.fn (fun j => x (i.succAbove j))) := by
  have hp : HasCompactSupport (fun z : Space × Configuration N => φ.fn z.1 * η.fn z.2) := by
    apply HasCompactSupport.of_support_subset_isCompact (φ.compact.prod η.compact)
    intro z hz
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz
    exact ⟨subset_tsupport _ hz.1, subset_tsupport _ hz.2⟩
  exact hp.comp_homeomorph (coordinateSplit i).toHomeomorph

end CoulombAtom.Pauli

end

end OAI
