import OAI.Probability.SLE.StoppedMeasures

namespace OAI

/-! The reverse Loewner equation determines the inverse maps and hence
the continuous trace. This is deterministic uniqueness for a fixed driver. -/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge

theorem IsCapacityTwoWitness.inverse_unique
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F H J : ℝ≥0 → ℂ → ℂ}
    (hγ : IsCapacityTwoWitness U γ G F) (hβ : IsCapacityTwoWitness U β H J)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ upperHalfPlane) : F T z = J T z := by
  let Q : ℝ → ℂ := fun t => G ((T : ℝ) - t).toNNReal (F T z)
  have hQ0 : Q 0 = z := by
    simp only [Q, sub_zero, Real.toNNReal_coe]
    exact hγ.2.2.2.2.2.2.2.2.1 T z hz
  have hQt : Q T = F T z := by
    simp only [Q, sub_self, Real.toNNReal_zero]
    exact hγ.initial_value _ (hγ.2.2.2.2.2.2.1 T hz).1.1
  have he := hβ.reverse_flow_identifies T z hz le_rfl Q hQ0
    (fun t ht => hγ.reverse_path_derivative T z hz le_rfl t ht)
  rwa [hQt] at he

theorem IsCapacityTwoWitness.trace_unique
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F H J : ℝ≥0 → ℂ → ℂ}
    (hγ : IsCapacityTwoWitness U γ G F) (hβ : IsCapacityTwoWitness U β H J) : γ = β := by
  funext T
  let y : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hy : Tendsto y atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => by change 0 < y n; dsimp only [y]; positivity)⟩
  have he (n : ℕ) : F T ((U T : ℂ) + (y n : ℂ) * Complex.I) =
      J T ((U T : ℂ) + (y n : ℂ) * Complex.I) := by
    apply hγ.inverse_unique hβ
    change 0 < ((U T : ℂ) + (y n : ℂ) * Complex.I).im
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
      zero_add] using (show 0 < y n by dsimp only [y]; positivity)
  exact tendsto_nhds_unique (hγ.2.2.2.2.2.2.2.2.2.2.2.2 T |>.comp hy)
    ((hβ.2.2.2.2.2.2.2.2.2.2.2.2 T |>.comp hy).congr (fun n => (he n).symm))

theorem IsCapacityTwoTrace.unique {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ}
    (hγ : IsCapacityTwoTrace U γ) (hβ : IsCapacityTwoTrace U β) : γ = β := by
  obtain ⟨G, F, hγ⟩ := hγ
  obtain ⟨H, J, hβ⟩ := hβ
  exact hγ.trace_unique hβ

end SLEExactGauge

end

end OAI
