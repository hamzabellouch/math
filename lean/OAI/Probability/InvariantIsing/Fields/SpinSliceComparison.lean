import OAI.Probability.InvariantIsing.Fields.SpinHammingBall

namespace OAI

/-! Deterministic comparison of restricted pressures through bounded
spin-flip maps, including the multiplicity cost of those maps. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma rotated_spin_energy_map_bound {N : ℕ} (eig c : Fin N → ℝ) (U : Rotation N)
    (σ τ : Spin N) (d : ℕ) (hd : hammingDist σ τ ≤ d)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (heig : ∀ i, |eig i| ≤ K) (hc : ∀ i, |c i| ≤ C) :
    |(rotatedEnergy eig U σ + fieldEnergy c σ) -
      (rotatedEnergy eig U τ + fieldEnergy c τ)| ≤
      2 * K * Real.sqrt ((N : ℝ) * d) + 2 * C * d := by
  have hd' : (hammingDist σ τ : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hquad := abs_rotatedEnergy_sub_spin_le eig U σ τ hK heig
  have hfield := abs_fieldEnergy_sub_spin_le c σ τ hc
  have hsqrt : Real.sqrt ((N : ℝ) * (hammingDist σ τ : ℝ)) ≤
      Real.sqrt ((N : ℝ) * d) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hd' (Nat.cast_nonneg _))
  have he : (rotatedEnergy eig U σ + fieldEnergy c σ) -
      (rotatedEnergy eig U τ + fieldEnergy c τ) =
      (rotatedEnergy eig U σ - rotatedEnergy eig U τ) +
        (fieldEnergy c σ - fieldEnergy c τ) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add
    (hquad.trans (mul_le_mul_of_nonneg_left hsqrt (by positivity)))
    (hfield.trans (mul_le_mul_of_nonneg_left hd' (by positivity))))

lemma restricted_spin_pressure_map_le {N : ℕ} (S T : Finset (Spin N))
    (hS : S.Nonempty) (hT : T.Nonempty) (f : Spin N → Spin N)
    (eig c : Fin N → ℝ) (U : Rotation N) (d : ℕ)
    {K C t : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (heig : ∀ i, |eig i| ≤ K) (hc : ∀ i, |c i| ≤ C)
    (hf : ∀ σ ∈ S, f σ ∈ T) (hd : ∀ σ ∈ S, hammingDist σ (f σ) ≤ d) :
    restrictedSpinLog S (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) ≤
      restrictedSpinLog T (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) +
      (2 * K * Real.sqrt ((N : ℝ) * d) + 2 * C * d) +
      t * d + N * Real.log (1 + Real.exp (-t)) := by
  apply restrictedSpinLog_le_of_hamming_map S T hS hT f _ _ _ d ht hf hd
  intro σ hσ
  have hh := rotated_spin_energy_map_bound eig c U σ (f σ) d (hd σ hσ) hK hC heig hc
  linarith [(le_abs_self _).trans hh]

lemma abs_restricted_spin_pressure_sub_le {N : ℕ} (S T : Finset (Spin N))
    (hS : S.Nonempty) (hT : T.Nonempty) (f g : Spin N → Spin N)
    (eig c : Fin N → ℝ) (U : Rotation N) (d : ℕ)
    {K C t : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (heig : ∀ i, |eig i| ≤ K) (hc : ∀ i, |c i| ≤ C)
    (hf : ∀ σ ∈ S, f σ ∈ T) (hd : ∀ σ ∈ S, hammingDist σ (f σ) ≤ d)
    (hg : ∀ τ ∈ T, g τ ∈ S) (he : ∀ τ ∈ T, hammingDist τ (g τ) ≤ d) :
    |restrictedSpinLog S (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) -
      restrictedSpinLog T (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)| ≤
      2 * K * Real.sqrt ((N : ℝ) * d) + 2 * C * d +
      t * d + N * Real.log (1 + Real.exp (-t)) := by
  have h₁ := restricted_spin_pressure_map_le S T hS hT f eig c U d hK hC ht heig hc hf hd
  have h₂ := restricted_spin_pressure_map_le T S hT hS g eig c U d hK hC ht heig hc hg he
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end InvariantIsing

end

end OAI
