import OAI.Geometry.NodalSets.Elliptic.CutoffProduct
import OAI.Geometry.NodalSets.Waves.ExponentialWaveBounds

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma mul_derivative_power_bound {f u : Coord → ℂ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) (k : ℕ) (x : Coord)
    {A B N w : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hfa : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ A * N ^ j)
    (hub : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j u x‖ ≤ B * N ^ j * w) :
    ‖iteratedFDeriv ℝ k (fun z ↦ f z * u z) x‖ ≤ (2 : ℝ) ^ k * A * B * N ^ k * w := by
  have h := norm_iteratedFDeriv_mul_le hf hu x (n := k)
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  calc
    _ ≤ _ := h
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (A * B * N ^ k * w) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
      have hm := mul_le_mul (hfa j hjk) (hub (k - j) (Nat.sub_le _ _))
        (norm_nonneg _) (mul_nonneg hA (pow_nonneg hN _))
      have he : (A * N ^ j) * (B * N ^ (k - j) * w) = A * B * N ^ k * w := by
        rw [show (A * N ^ j) * (B * N ^ (k - j) * w) =
          A * B * (N ^ j * N ^ (k - j)) * w by ring, ← pow_add, Nat.add_sub_of_le hjk]
      rw [he] at hm
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (k.choose j))
    _ = _ := by
      rw [← Finset.sum_mul]
      have he : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = (2 : ℝ) ^ k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [he]
      ring

theorem cutoff_wave_size (k : ℕ) : ∃ B > 0, ∀ (phi a : Coord → ℂ),
    ContDiff ℝ ∞ phi → ContDiff ℝ ∞ a → ∀ (y x : Coord) (N A D S c : ℝ),
    1 ≤ N → 0 ≤ A → 1 ≤ D →
    (∀ j, j ≤ k → ‖iteratedFDeriv ℝ j a x‖ ≤ A) →
    (∀ j, 1 ≤ j → j ≤ k → ‖iteratedFDeriv ℝ j phi x‖ ≤ D) →
    (phi x).re - S ≤ -c * ‖x - y‖ ^ 2 →
    ‖iteratedFDeriv ℝ k (fun z ↦ Yau.Waves.scaledCutoff N y z •
      (a z * waveExp phi N z)) x‖ ≤
      B * A * (k.factorial : ℝ) * D ^ k * N ^ k *
        Real.exp (N * S - c * N * ‖x - y‖ ^ 2) := by
  obtain ⟨B, hB, hcut⟩ := Yau.Waves.cutoff_preserves_derivative_exponent (E := Coord) (F := ℂ) k
  refine ⟨(2 : ℝ) ^ k * B * (2 : ℝ) ^ k, by positivity, ?_⟩
  intro phi a hp ha y x N A D S c hN hA hD hamp hphase hgap
  let w := Real.exp (N * S - c * N * ‖x - y‖ ^ 2)
  let Q := (k.factorial : ℝ) * D ^ k
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hw : 0 ≤ w := (Real.exp_pos _).le
  have he (j : ℕ) (hj : j ≤ k) : ‖iteratedFDeriv ℝ j (waveExp phi N) x‖ ≤ Q * N ^ j * w := by
    apply (waveExp_gaussian_derivative_bound hp j x hD hN
      (fun i hi hij ↦ hphase i hi (hij.trans hj)) hgap).trans
    have hfact : (j.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hj
    have hpow : D ^ j ≤ D ^ k := pow_le_pow_right₀ hD hj
    dsimp [Q, w]
    gcongr
  have hau (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (fun z ↦ a z * waveExp phi N z) x‖ ≤
        ((2 : ℝ) ^ k * A * Q) * N ^ j * w := by
    apply (mul_derivative_power_bound ha (waveExp_contDiff hp N) j x hA
      (le_trans zero_le_one hN) _ (fun i hi ↦ he i (hi.trans hj))).trans
    · have hp2 : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
      gcongr
    · intro i hi
      exact (hamp i (hi.trans hj)).trans (le_mul_of_one_le_right hA (one_le_pow₀ hN))
  have h := hcut N hN y x (fun z ↦ a z * waveExp phi N z) (ha.mul (waveExp_contDiff hp N))
    ((2 : ℝ) ^ k * A * Q) w (by positivity) hw hau
  convert h using 1
  dsimp [Q, w]
  ring

end
end Yau.Jets

end OAI
