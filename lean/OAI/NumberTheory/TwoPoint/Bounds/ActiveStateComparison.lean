import OAI.NumberTheory.TwoPoint.Bounds.ActiveStateVectors
import OAI.NumberTheory.TwoPoint.Bounds.EventualResidueComparison

namespace OAI

/-! Arbitrary functions of the bounded active sets at the trace vertices
are compared at every finite interval, using their exact state expansion. -/

namespace TwoPointCorrelations

open Finset Filter

theorem BravermanDepth22Input.eventually_active_state_comparison (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (R n Ninput M : ℕ), (n : ℝ) ≤ Real.exp L →
      (M : ℝ) ≤ 400 * Real.log L → (R : ℝ) ≤ 4 * L →
      ∀ (coord : Fin Ninput → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool)
        (index : Fin R → Fin n → Fin Ninput)
        (f : (Fin R → Finset (Fin n)) → ℝ),
      (∀ b : Fin R → boundedActiveStates n M,
        |f (fun r => (b r).val)| ≤ Real.exp (L ^ 4)) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun z : ∀ j, ZMod (s j) =>
        let bits := residueCircuitInputs s coord test z
        if ∀ r, (activeState (fun i => bits (index r i))).card ≤ M
        then f (fun r => activeState (fun i => bits (index r i))) else 0
      |uniformAverage (fun x : Fin N => F (fun j => (a + x.val : ZMod (s j)))) -
        uniformAverage F| ≤ Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hscalar⟩ := hBr.eventually_scalar_residue_comparison 1 (by norm_num)
  refine ⟨A, hA, ?_⟩
  filter_upwards [hscalar, eventually_ge_atTop (4800 : ℝ)] with L hscalar hL
  intro m s _ hm hmexp hcop hs R n Ninput M hn hM hR coord test index f hf a N hN
  let c := fun b : Fin R → boundedActiveStates n M =>
    activeStateVectorCircuit index (fun r => (b r).val)
  let coeff := fun b : Fin R → boundedActiveStates n M => f (fun r => (b r).val)
  have hb := hscalar m s hm hmexp hcop hs _ Ninput coord test c coeff
    (fun b => (activeStateVectorCircuit_depth index _).trans (by norm_num))
    (fun b => activeStateVector_size_budget L index _ (by linarith) hn hR)
    (by simpa only [one_mul] using activeStateVector_coefficient_budget L f hL hn hM hR hf)
    a N hN
  have hexpand (z : ∀ j, ZMod (s j)) :
      (if ∀ r, (activeState (fun i => residueCircuitInputs s coord test z (index r i))).card ≤ M
        then f (fun r => activeState (fun i => residueCircuitInputs s coord test z (index r i))) else 0) =
        ∑ b : Fin R → boundedActiveStates n M, coeff b *
          eventIndicator (residueCircuitEvent s coord test (c b)) z :=
    activeStateVector_scalar_expansion M index f (residueCircuitInputs s coord test z)
  dsimp only
  simpa only [← hexpand] using hb

end TwoPointCorrelations

end OAI
