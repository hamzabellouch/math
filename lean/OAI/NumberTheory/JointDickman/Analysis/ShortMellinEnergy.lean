import OAI.NumberTheory.JointDickman.Analysis.ShortMellinComparison
import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicEnergyTransfer

namespace OAI

/-! # Short-average energy from the actual Dirichlet polynomial on a block -/
namespace JointDickman
open Finset MeasureTheory PublishedInputs

/-- A linear spectral bound yields a uniform bound for the original short
averages. The coefficient range is explicit and the smoothing error tends to
zero with the block width, profile transition width, and endpoint scales. -/
theorem shortAverage_block_energy_of_support (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ArithmeticFunction ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ (K N : ℕ) (X H ε : ℝ), 0 < X → 1 ≤ H → H ≤ X → 0 ≤ ε → ε ≤ 1 →
      K ≤ ⌊X⌋₊ → ⌊(1 + ε) * (X + H)⌋₊ ≤ N →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ T : ℝ, 1 ≤ T →
        (∫ t in -T..T, ‖mellinPolynomial
          (Ioc K N) f t‖ ^ 2) ≤ A + B * T) →
      (1 / X) * (∫ x in X..(1 + ε) * X, ‖complexShortAverage f H x‖ ^ 2) ≤
        C * (A + B * X / H) +
          2 * ε * (3 * ε + 11 / H + H / X + 1 / X + 16 * η) ^ 2 := by
  obtain ⟨C, hC, hCbound⟩ :=
    mellinPacket_energy_of_spectral_bound (logarithmicWindowProfile η hη hηhalf)
  refine ⟨8 * C, by positivity, ?_⟩
  intro f hf K N X H ε hX hH hHX hε hε1 hK hN A B hA hB hspectral
  have hH0 : 0 < H := by linarith
  let δ := Real.log ((X + H) / X)
  have hwidth := logarithmic_window_width hX hH0
  have hδ : 0 < δ := hwidth.1
  have hδ1 : δ ≤ 1 := hwidth.2.2.trans ((div_le_one hX).mpr hHX)
  let Y := (1 + ε) * X
  have hXY : X ≤ Y := by dsimp [Y]; nlinarith
  have hY2 : Y ≤ 2 * X := by dsimp [Y]; nlinarith
  let P := mellinPacket (Ioc K N) f
    (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
  let E := 3 * ε + 11 / H + H / X + 1 / X + 16 * η
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hP : (∫ v : ℝ, ‖P v‖ ^ 2) ≤ C * (A + B / δ) :=
    hCbound _ _ δ hδ hδ1 A B hA hB hspectral
  have hPnonneg : 0 ≤ ∫ v : ℝ, ‖P v‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hlog : ContinuousOn (fun x => ‖P (Real.log x + δ)‖ ^ 2) (Set.uIcc X Y) := by
    rw [Set.uIcc_of_le hXY]
    intro x hx
    exact ((P.continuous.continuousAt.comp ((Real.continuousAt_log
      (hX.trans_le hx.1).ne').add_const δ)).norm.pow 2).continuousWithinAt
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc X Y) :
      ‖complexShortAverage f H x‖ ^ 2 ≤ 2 * ‖P (Real.log x + δ)‖ ^ 2 + 2 * E ^ 2 := by
    have hh := shortAverage_le_mellinPacket_of_support f hf hX hH hHX hη hηhalf hx hK hN
    change ‖complexShortAverage f H x‖ ≤ ‖P (Real.log x + δ)‖ + E at hh
    have hn := norm_nonneg (complexShortAverage f H x)
    have hp := norm_nonneg (P (Real.log x + δ))
    nlinarith [sq_nonneg (‖P (Real.log x + δ)‖ - E)]
  have hshort : (∫ x in X..Y, ‖complexShortAverage f H x‖ ^ 2) ≤
      2 * Y * (C * (A + B / δ)) + 2 * (Y - X) * E ^ 2 := by
    calc
      _ ≤ ∫ x in X..Y, 2 * ‖P (Real.log x + δ)‖ ^ 2 + 2 * E ^ 2 :=
        intervalIntegral.integral_mono_on hXY (complexShortAverage_sq_integrable f hf hH0 X Y)
          ((hlog.const_mul 2).add continuousOn_const).intervalIntegrable hpoint
      _ = 2 * (∫ x in X..Y, ‖P (Real.log x + δ)‖ ^ 2) + 2 * (Y - X) * E ^ 2 := by
        rw [intervalIntegral.integral_add (hlog.const_mul 2).intervalIntegrable intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ 2 * (Y * ∫ v : ℝ, ‖P v‖ ^ 2) + 2 * (Y - X) * E ^ 2 := by
        gcongr
        exact schwartz_logarithmic_energy_le P hX hXY δ
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hP (show 0 ≤ 2 * Y by positivity)
        nlinarith only [hh]
  have hlow : H ≤ 2 * δ * X := by
    have hh := (div_le_iff₀ (show 0 < X + H by linarith)).mp hwidth.2.1
    have hmul := mul_le_mul_of_nonneg_left hHX hδ.le
    nlinarith
  have hBδ : B / δ ≤ 2 * (B * X / H) := by
    calc
      B / δ ≤ (2 * B * X) / H := by
        apply (div_le_div_iff₀ hδ hH0).mpr
        nlinarith [mul_le_mul_of_nonneg_left hlow hB]
      _ = _ := by ring
  have hbudget : 2 * Y * (C * (A + B / δ)) ≤ 8 * C * X * (A + B * X / H) := by
    have hsmall : 0 ≤ B * X / H := by positivity
    have hfirst : 2 * Y * (C * (A + B / δ)) ≤
        2 * (2 * X) * (C * (A + 2 * (B * X / H))) := by gcongr
    nlinarith [mul_nonneg (by positivity : 0 ≤ C * X) hA]
  have hscaled := mul_le_mul_of_nonneg_left (hshort.trans (add_le_add hbudget (le_refl (2 * (Y - X) * E ^ 2))))
    (show 0 ≤ 1 / X by positivity)
  have hright : (1 / X) * (8 * C * X * (A + B * X / H) + 2 * (Y - X) * E ^ 2) =
      8 * C * (A + B * X / H) + 2 * ε * E ^ 2 := by
    dsimp [Y]
    field_simp
    ring
  rw [hright] at hscaled
  exact hscaled

theorem shortAverage_block_energy (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ArithmeticFunction ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ X H ε : ℝ, 0 < X → 1 ≤ H → H ≤ X → 0 ≤ ε → ε ≤ 1 →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ T : ℝ, 1 ≤ T →
        (∫ t in -T..T, ‖mellinPolynomial
          (Ioc ⌊X⌋₊ ⌊(1 + ε) * (X + H)⌋₊) f t‖ ^ 2) ≤ A + B * T) →
      (1 / X) * (∫ x in X..(1 + ε) * X, ‖complexShortAverage f H x‖ ^ 2) ≤
        C * (A + B * X / H) +
          2 * ε * (3 * ε + 11 / H + H / X + 1 / X + 16 * η) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := shortAverage_block_energy_of_support η hη hηhalf
  refine ⟨C, hC, ?_⟩
  intro f hf X H ε hX hH hHX hε hε1 A B hA hB hspectral
  exact hbound f hf _ _ X H ε hX hH hHX hε hε1 le_rfl le_rfl A B hA hB hspectral

end JointDickman

end OAI
