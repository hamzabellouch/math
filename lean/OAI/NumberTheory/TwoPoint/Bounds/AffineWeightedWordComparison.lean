import OAI.NumberTheory.TwoPoint.Walks.WeightedWordComparison
import OAI.NumberTheory.TwoPoint.Bounds.AffineResidueAverage

namespace OAI

/-! The existing signed word comparison on each fixed progression class.
All state, circuit and coefficient budgets remain unchanged. -/

namespace TwoPointCorrelations

open Finset Filter

theorem BravermanDepth22Input.eventually_affine_weighted_word_comparison
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
      ∀ a l N : ℕ, (∀ i, l.Coprime (s i)) → Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun z : ∀ j, ZMod (s j) =>
        let bits := residueCircuitInputs s coord test z
        if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
        then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
        else 0
      |uniformAverage (fun x : Fin N => F (fun j => (a + l * x.val : ZMod (s j)))) -
        uniformAverage F| ≤ Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hbase⟩ := hBr.eventually_weighted_word_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbase] with L hbase
  intro m s _ hm hmexp hcop hs R n t Ninput M hn hM hR ht coord test qindex pindex f c hf hc hsize a l N hl hN
  let affineTest := fun i (z : ZMod (s (coord i))) =>
    test i ((a : ZMod (s (coord i))) + (l : ZMod (s (coord i))) * z)
  let F := fun z : ∀ j, ZMod (s j) =>
    let bits := residueCircuitInputs s coord test z
    if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
    then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
    else 0
  let G := fun z : ∀ j, ZMod (s j) =>
    let bits := residueCircuitInputs s coord affineTest z
    if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
    then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
    else 0
  have hbits (z : ∀ j, ZMod (s j)) : residueCircuitInputs s coord affineTest z =
      residueCircuitInputs s coord test (fun j => (a : ZMod (s j)) + (l : ZMod (s j)) * z j) := rfl
  have hG (z : ∀ j, ZMod (s j)) : G z =
      F (fun j => (a : ZMod (s j)) + (l : ZMod (s j)) * z j) := by
    dsimp only [G, F]
    rw [hbits]
  have hb := hbase m s hm hmexp hcop hs R n t Ninput M hn hM hR ht
    coord affineTest qindex pindex f c hf hc hsize 0 N hN
  change |uniformAverage (fun x : Fin N => G (fun j => ((0 : ℕ) : ZMod (s j)) + x.val)) -
    uniformAverage G| ≤ Real.exp (-(L ^ 9)) at hb
  have hGfun : G = fun z => F (fun j => (a : ZMod (s j)) + (l : ZMod (s j)) * z j) := funext hG
  rw [hGfun] at hb
  rw [uniformAverage_residue_affine s a l hl F] at hb
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_zero, zero_add] using hb

end TwoPointCorrelations

end OAI
