import OAI.NumberTheory.TwoPoint.Walks.WeightedWordBudget
import OAI.NumberTheory.TwoPoint.Bounds.EventualResidueComparison

namespace OAI

/-! Finite-origin comparison for signed weighted words. All centered
prime bits, bounded padding states, and the surviving-site circuit are
expanded together, before taking any absolute values. -/

namespace TwoPointCorrelations

open Finset Filter

theorem BravermanDepth22Input.eventually_weighted_word_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (R n t Ninput M : ℕ), (n : ℝ) ≤ Real.exp L →
      (M : ℝ) ≤ 400 * Real.log L → (R : ℝ) ≤ 4 * L → (t : ℝ) ≤ L ^ 2 →
      ∀ (coord : Fin Ninput → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool)
        (qindex : Fin R → Fin n → Fin Ninput) (pindex : Fin t → Fin Ninput)
        (f : (Fin R → Finset (Fin n)) → BooleanCube t → ℝ) (c : AC0Circuit Ninput),
      (∀ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
        |f (fun r => (b.1 r).val) b.2| ≤ Real.exp (L ^ 4)) →
      c.depth ≤ 19 → (c.size : ℝ) ≤ Real.exp (L ^ 3) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun z : ∀ j, ZMod (s j) =>
        let bits := residueCircuitInputs s coord test z
        if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
        then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
        else 0
      |uniformAverage (fun x : Fin N => F (fun j => (a + x.val : ZMod (s j)))) -
        uniformAverage F| ≤ Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hscalar⟩ := hBr.eventually_scalar_residue_comparison 1 (by norm_num)
  refine ⟨A, hA, ?_⟩
  filter_upwards [hscalar, eventually_ge_atTop (4800 : ℝ)] with L hscalar hL
  intro m s _ hm hmexp hcop hs R n t Ninput M hn hM hR ht coord test qindex pindex f c hf hc hsize a N hN
  let circuits := fun b : (Fin R → boundedActiveStates n M) × BooleanCube t =>
    weightedStateCircuit qindex pindex (fun r => (b.1 r).val) b.2 c
  let coeff := fun b : (Fin R → boundedActiveStates n M) × BooleanCube t =>
    f (fun r => (b.1 r).val) b.2
  have hb := hscalar m s hm hmexp hcop hs _ Ninput coord test circuits coeff
    (fun b => weightedStateCircuit_depth qindex pindex _ _ c hc)
    (fun b => weightedStateCircuit_size_budget L qindex pindex _ _ c (by linarith) hn hR ht hsize)
    (by simpa only [one_mul] using weightedWord_coefficient_budget L f hL hn hM hR ht hf)
    a N hN
  have hexpand (z : ∀ j, ZMod (s j)) :
      (if (∀ r, (activeState (fun i => residueCircuitInputs s coord test z (qindex r i))).card ≤ M) ∧
          c.eval (residueCircuitInputs s coord test z) = true
        then f (fun r => activeState (fun i => residueCircuitInputs s coord test z (qindex r i)))
          (fun i => residueCircuitInputs s coord test z (pindex i)) else 0) =
      ∑ b : (Fin R → boundedActiveStates n M) × BooleanCube t, coeff b *
        eventIndicator (residueCircuitEvent s coord test (circuits b)) z :=
    weightedWord_scalar_expansion M qindex pindex f c (residueCircuitInputs s coord test z)
  dsimp only
  simpa only [← hexpand] using hb

end TwoPointCorrelations

end OAI
