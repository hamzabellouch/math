import OAI.Combinatorics.EditApproximation.Geometry.BandGroupSampling

namespace OAI

/-! The shared group samples cancel the reciprocal envelope factor in
the number of possible rounded child inputs, including exact evaluation. -/

namespace EditApproximation

theorem groupSampleCount_shared_work {M Q b : ℕ} {h : ℚ}
    (hM : 0 < M) (hQ : 1 ≤ Q) (hb : 0 < b) (hh : 0 < h)
    (hfloor : (b : ℚ) / M ≤ h) :
    (groupSampleCount M Q b h : ℚ) * (1 + b / h) ≤ 3 * Q * M := by
  have hMr : (0 : ℚ) < M := by exact_mod_cast hM
  have hQr : (1 : ℚ) ≤ Q := by exact_mod_cast hQ
  have hbr : (0 : ℚ) < b := by exact_mod_cast hb
  have hMh : (b : ℚ) ≤ M * h := by
    nlinarith only [(div_le_iff₀ hMr).mp hfloor]
  have hQproduct := mul_le_mul_of_nonneg_right hQr (show (0 : ℚ) ≤ M * h by positivity)
  have hx : (1 : ℚ) ≤ Q * M * h / b := by
    apply (le_div_iff₀ hbr).2
    nlinarith only [hMh, hQproduct]
  have hceil : (⌈(Q : ℚ) * M * h / b⌉₊ : ℚ) < (Q : ℚ) * M * h / b + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hkM : (groupSampleCount M Q b h : ℚ) ≤ M := by
    unfold groupSampleCount
    exact_mod_cast (min_le_left M ⌈(Q : ℚ) * M * h / b⌉₊)
  have hkceil : (groupSampleCount M Q b h : ℚ) ≤ ⌈(Q : ℚ) * M * h / b⌉₊ := by
    unfold groupSampleCount
    exact_mod_cast (min_le_right M ⌈(Q : ℚ) * M * h / b⌉₊)
  have hkX : (groupSampleCount M Q b h : ℚ) ≤ 2 * ((Q : ℚ) * M * h / b) := by
    linarith only [hkceil, hceil, hx]
  have hkb : (groupSampleCount M Q b h : ℚ) * b ≤ 2 * Q * M * h := by
    apply (le_div_iff₀ hbr).mp
    convert hkX using 1
    ring
  have hreciprocal : (groupSampleCount M Q b h : ℚ) * b / h ≤ 2 * Q * M :=
    (div_le_iff₀ hh).2 hkb
  have hQM := mul_le_mul_of_nonneg_right hQr hMr.le
  calc
    _ = (groupSampleCount M Q b h : ℚ) + (groupSampleCount M Q b h : ℚ) * b / h := by ring
    _ ≤ (M : ℚ) + 2 * Q * M := add_le_add hkM hreciprocal
    _ ≤ 3 * Q * M := by nlinarith only [hQM]

theorem groupDyadicScale_shared_work {M Q b : ℕ} {F h : ℚ}
    (hM : 0 < M) (hQ : 1 ≤ Q) (hb : 0 < b) (hF : 0 < F)
    (hh : h ∈ groupDyadicScales M b F) :
    (groupSampleCount M Q b h : ℚ) * (1 + b / h) ≤ 3 * Q * M := by
  have hpos := groupDyadicScales_pos hh
  obtain ⟨exponent, hexponent, heq⟩ := List.mem_map.mp hh
  have hbounds := (groupDyadicScales_mem hM hb F hF exponent).mp
    (List.mem_map.mpr ⟨exponent, hexponent, rfl⟩)
  exact groupSampleCount_shared_work hM hQ hb hpos (heq ▸ hbounds.1)

end EditApproximation

end OAI
