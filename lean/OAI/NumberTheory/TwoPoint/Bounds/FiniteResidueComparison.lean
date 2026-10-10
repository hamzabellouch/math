import OAI.NumberTheory.TwoPoint.Bounds.DecoderComparison

namespace OAI

/-!
# Finite residue-circuit comparison

An original residue circuit has depth at most twenty. Each input tests one
residue coordinate, and is replaced by its explicit truth table on the
corresponding bit block. The encoded circuit therefore has depth at most
twenty-two. The empirical Fourier bound, the published Braverman input,
and the two decoding errors give a completely finite error estimate.
-/

namespace TwoPointCorrelations

open Finset

lemma abs_add_three (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le (a + b) c).trans (add_le_add (abs_add_le a b) (le_refl |c|))

/-- Inputs to an actual Boolean circuit, with each input depending on one
specified residue coordinate. Equality with a fixed residue is a special case. -/
def residueCircuitInputs {n m : ℕ} (s : Fin m → ℕ) (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (r : ∀ j, ZMod (s j)) : BooleanCube n :=
  fun i => test i (r (coord i))

def residueCircuitEvent {n m : ℕ} (s : Fin m → ℕ) (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n)
    (r : ∀ j, ZMod (s j)) : Bool := c.eval (residueCircuitInputs s coord test r)

/-- The actual truth-table circuit used for encoded residue testing. -/
noncomputable def encodeResidueCircuit {n m : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (B : ℕ) (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n) : AC0Circuit (m * B) :=
  AC0Circuit.encodeInputs (fun i j => finProdFinEquiv (coord i, j))
    (fun i z => test i (ZMod.finEquiv (s (coord i))
      (decodeBits (NeZero.pos (s (coord i))) z))) c

lemma flattenBitBlocks_block {m B : ℕ} (z : Fin m → BooleanCube B) (i : Fin m) :
    (fun j => flattenBitBlocks m B z (finProdFinEquiv (i, j))) = z i := by
  funext j
  exact congrArg (fun p : Fin m × Fin B => z p.1 p.2)
    (finProdFinEquiv.symm_apply_apply (i, j))

lemma encodeResidueCircuit_eval {n m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n)
    (z : Fin m → BooleanCube B) :
    (encodeResidueCircuit s B coord test c).eval (flattenBitBlocks m B z) =
      residueCircuitEvent s coord test c (decodedResidues s B z) := by
  unfold encodeResidueCircuit
  rw [AC0Circuit.encodeInputs_eval]
  simp only [flattenBitBlocks_block]
  rfl

lemma encodeResidueCircuit_indicator {n m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n)
    (z : Fin m → BooleanCube B) :
    (encodeResidueCircuit s B coord test c).indicator (flattenBitBlocks m B z) =
      eventIndicator (residueCircuitEvent s coord test c) (decodedResidues s B z) := by
  simp only [AC0Circuit.indicator, eventIndicator, encodeResidueCircuit_eval]

lemma encodeResidueCircuit_depth {n m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n) :
    (encodeResidueCircuit s B coord test c).depth ≤ c.depth + 2 :=
  AC0Circuit.encodeInputs_depth _ _ c

lemma encodeResidueCircuit_size {n m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n) :
    (encodeResidueCircuit s B coord test c).size ≤ (1 + 2 ^ B * (1 + B)) * c.size :=
  AC0Circuit.encodeInputs_size _ _ c

lemma encodeResidueCircuit_interval_average {n m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n) (a N : ℕ) :
    uniformAverage (fun x : Fin N × (Fin m → Fin (2 ^ B)) =>
      (encodeResidueCircuit s B coord test c).indicator (integerBitSample s B a x)) =
    uniformAverage (fun x : Fin N => uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
      eventIndicator (residueCircuitEvent s coord test c)
        (decodedResidues s B (crtJitterBits s B (fun i => (a + x.val : ZMod (s i))) j)))) := by
  change uniformAverage (fun x : Fin N × (Fin m → Fin (2 ^ B)) =>
    (encodeResidueCircuit s B coord test c).indicator
      (flattenBitBlocks m B (crtJitterBits s B (fun i => (a + x.1.val : ZMod (s i))) x.2))) = _
  simp_rw [encodeResidueCircuit_indicator]
  exact uniformAverage_prod (fun (x : Fin N) (j : Fin m → Fin (2 ^ B)) =>
    eventIndicator (residueCircuitEvent s coord test c)
      (decodedResidues s B (crtJitterBits s B (fun i => (a + x.val : ZMod (s i))) j)))

lemma encodeResidueCircuit_uniform_average {n m B : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (coord : Fin n → Fin m)
    (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n) :
    cubeAverage (encodeResidueCircuit s B coord test c).indicator =
    uniformAverage (fun r : ∀ i, ZMod (s i) =>
      uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
        eventIndicator (residueCircuitEvent s coord test c)
          (decodedResidues s B (crtJitterBits s B r j)))) := by
  calc
    _ = uniformAverage (fun z : Fin m → BooleanCube B =>
        (encodeResidueCircuit s B coord test c).indicator (flattenBitBlocks m B z)) :=
      (uniformAverage_equiv (flattenBitBlocks m B)
        (encodeResidueCircuit s B coord test c).indicator).symm
    _ = uniformAverage (fun r : ∀ i, ZMod (s i) =>
        uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
          (encodeResidueCircuit s B coord test c).indicator
            (flattenBitBlocks m B (crtJitterBits s B r j)))) :=
      (crtJitterBits_uniformAverage s B _).symm
    _ = _ := by simp_rw [encodeResidueCircuit_indicator]

/-- Comparison for the original depth-twenty residue circuit. The arithmetic
hypotheses are precisely positivity and pairwise coprimality of the moduli;
no squarefreeness or bound on their total product is used. The low-order
Fourier error and the decoding error are explicit finite quantities. -/
theorem BravermanDepth22Input.finite_residue_comparison (hBraverman : BravermanDepth22Input) :
    ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ (m B : ℕ), 0 < m * B →
      ∀ (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      Pairwise (fun i j => (s i).Coprime (s j)) →
      ∀ (n : ℕ) (coord : Fin n → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool) (c : AC0Circuit n), c.depth ≤ 20 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log
          (((encodeResidueCircuit s B coord test c).size : ℝ) / ε)) ^ C ≤ (t : ℝ) →
        ∀ (a N : ℕ), 0 < N → ∀ M A : ℝ, 1 ≤ M → (∀ i, (s i : ℝ) ≤ M) →
          (M ^ t / (N : ℝ)) * ((t + 1 : ℕ) : ℝ) * ((m * B : ℕ) : ℝ) ^ t ≤ A →
          |uniformAverage (fun x : Fin N =>
              eventIndicator (residueCircuitEvent s coord test c)
                (fun i => (a + x.val : ZMod (s i)))) -
            uniformAverage (eventIndicator (residueCircuitEvent s coord test c))| ≤
              2 * (∑ i : Fin m, (s i : ℝ) / (2 ^ B : ℕ)) + 3 * A / 2 + ε := by
  obtain ⟨K, C, hK, hC, hcompare⟩ := hBraverman.encoded_interval_comparison
  refine ⟨K, C, hK, hC, ?_⟩
  intro m B hn s _hpos hcop n coord test c hc ε hε hεmax t ht a N hN M A hM hs hA
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hdepth : (encodeResidueCircuit s B coord test c).depth ≤ 22 :=
    (encodeResidueCircuit_depth (B := B) s coord test c).trans (by omega)
  have hmiddle := hcompare m B hn s hcop (encodeResidueCircuit s B coord test c)
    hdepth ε hε hεmax t ht a N hN M A hM hs hA
  rw [encodeResidueCircuit_interval_average, encodeResidueCircuit_uniform_average] at hmiddle
  have hleft := decoder_event_error_averaged (B := B) s (residueCircuitEvent s coord test c)
    (fun x : Fin N => fun i => (a + x.val : ZMod (s i)))
  have hright := decoder_event_error_averaged (B := B) s (residueCircuitEvent s coord test c)
    (fun r : ∀ i, ZMod (s i) => r)
  let I := uniformAverage (fun x : Fin N =>
    eventIndicator (residueCircuitEvent s coord test c) (fun i => (a + x.val : ZMod (s i))))
  let J := uniformAverage (fun x : Fin N => uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
    eventIndicator (residueCircuitEvent s coord test c)
      (decodedResidues s B (crtJitterBits s B (fun i => (a + x.val : ZMod (s i))) j))))
  let U := uniformAverage (fun r : ∀ i, ZMod (s i) =>
    uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
      eventIndicator (residueCircuitEvent s coord test c)
        (decodedResidues s B (crtJitterBits s B r j))))
  let V := uniformAverage (eventIndicator (residueCircuitEvent s coord test c))
  change |I - J| ≤ _ at hleft
  change |J - U| ≤ _ at hmiddle
  change |V - U| ≤ _ at hright
  change |I - V| ≤ _
  have htriangle : |I - V| ≤ |I - J| + |J - U| + |U - V| := by
    calc
      _ = |(I - J) + (J - U) + (U - V)| := by congr 1; ring
      _ ≤ _ := abs_add_three (I - J) (J - U) (U - V)
  rw [abs_sub_comm] at hright
  linarith

end TwoPointCorrelations

end OAI
