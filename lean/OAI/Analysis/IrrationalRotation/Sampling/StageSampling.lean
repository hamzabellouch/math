import OAI.Analysis.IrrationalRotation.Sampling.SamplingHorizon
import OAI.Analysis.IrrationalRotation.Sampling.SyndeticSampling

namespace OAI

namespace Invariant233.StageSampling

open Filter

theorem exists_stage_with_phase_sampling {θ : ℝ} (hθ : Irrational θ)
    (j : ℕ) (hj : 0 < j) (K : ℕ) (G Gnext L H d : ℝ)
    (q : ℕ) (shift width : Fin q → ℝ) (hwidth : ∀ r, 0 < width r) :
    ∃ m : ℕ,
      K ≤ m ∧ (2 : ℝ) ^ j ≤ m ∧ 4 * G ≤ m ∧ 200 ≤ m ∧
      d ≤ (m : ℝ) / 100 ∧
      L ≤ (1 / (100 * (j : ℝ))) * (m : ℝ) ^ (1 / 40 : ℝ) ∧
      Gnext * (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) <
        (m : ℝ) ^ ((4 / 5 : ℝ) * m) ∧
      H / (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ≤ (1 / 2 : ℝ) ^ j ∧
      2 * (K : ℝ) < (⌈(m : ℝ) ^ ((3 / 4 : ℝ) * m)⌉₊ : ℝ) ∧
      ∃ t : Fin q → Finset ℕ, ∀ r : Fin q,
        (t r).Nonempty ∧
        (∀ n ∈ t r, (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n ∧
          (n : ℝ) ≤ (m : ℝ) ^ ((7 / 10 : ℝ) * m)) ∧
        (∀ n ∈ t r, Int.fract ((n : ℝ) * θ - shift r) ∈ Set.Ioo 0 (width r)) ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ ((t r).card : ℝ) ∧
        (∀ n ∈ t r, 0 < n) ∧
        ∀ n ∈ t r, ∀ n' ∈ t r, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
          (v ≠ 0 ∨ v' ≠ 0) →
          ((m * K) * m ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)| := by
  have hscalar := SamplingHorizon.eventually_stage_size j hj (K : ℝ) G Gnext L H d
  have hsampling := SyndeticSampling.eventually_exists_simultaneous_phase_sampling_powers
    hθ q shift width hwidth
  obtain ⟨m, hm, hs⟩ := (hscalar.and hsampling).exists
  obtain ⟨hK, htwo, hG, hm200, hd, hL, hgap, hheight, hdouble⟩ := hm
  have hKm : K ≤ m := by exact_mod_cast hK
  have hN : m * K ≤ m ^ 2 := by nlinarith
  obtain ⟨t, ht⟩ := hs (m * K) hN
  refine ⟨m, hKm, htwo, hG, hm200, hd, hL, hgap, hheight, hdouble, t, ?_⟩
  intro r
  have hpow : 0 < (m : ℝ) ^ ((69 / 100 : ℝ) * m) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < m by omega)) _
  have hcard : 0 < ((t r).card : ℝ) := hpow.trans_le (ht r).2.2.1
  have hnonempty : (t r).Nonempty := Finset.card_pos.mp (by exact_mod_cast hcard)
  exact ⟨hnonempty, ht r⟩

end Invariant233.StageSampling

end OAI
