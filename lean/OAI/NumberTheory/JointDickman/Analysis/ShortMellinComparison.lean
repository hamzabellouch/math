import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicWindowFreeze
import OAI.NumberTheory.JointDickman.Analysis.MellinWindowError

namespace OAI

/-! # Uniform approximation of the original short average on a small block -/
namespace JointDickman
open Finset PublishedInputs

/-- The coefficients are restricted to the same fixed block for every
location of the short interval; all errors are uniform on that block. -/
theorem shortAverage_le_mellinPacket_of_support (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {K N : ℕ} {X H ε η x : ℝ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (hη : 0 < η) (hηhalf : η < 1/2)
    (hx : x ∈ Set.Icc X ((1 + ε) * X))
    (hK : K ≤ ⌊X⌋₊) (hN : ⌊(1 + ε) * (X + H)⌋₊ ≤ N) :
    let δ := Real.log ((X + H) / X)
    let hδ := (logarithmic_window_width hX (by linarith : 0 < H)).1
    ‖complexShortAverage f H x‖ ≤
      ‖mellinPacket (Ioc K N) f
        (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
        (Real.log x + δ)‖ +
      (3 * ε + 11 / H + H / X + 1 / X + 16 * η) := by
  dsimp only
  let δ := Real.log ((X + H) / X)
  have hH0 : 0 < H := by linarith
  obtain ⟨hδ, hδlo, hδhi⟩ := logarithmic_window_width hX hH0
  have hδ1 : δ ≤ 1 := hδhi.trans ((div_le_one hX).mpr hHX)
  have hx0 : 0 < x := hX.trans_le hx.1
  have htop : x * Real.exp δ ≤ (1 + ε) * (X + H) := by
    dsimp [δ]
    rw [Real.exp_log (div_pos (by linarith) hX)]
    calc
      _ ≤ ((1 + ε) * X) * ((X + H) / X) :=
        mul_le_mul_of_nonneg_right hx.2 (by positivity)
      _ = _ := by field_simp
  have happrox := logarithmicWindowAverage_mellinPacket_error f hf hη hηhalf hδ hδ1 hx0
    (hK.trans (Nat.floor_mono hx.1)) ((Nat.floor_mono htop).trans hN)
  have hwindow := shortAverage_le_fixed_logarithmic_window f hf hX hH hx
  have hlower : H ≤ 2 * δ * x := by
    have hbase := (div_le_iff₀ (show 0 < X + H by linarith)).mp hδlo
    have hdouble : δ * (X + H) ≤ 2 * δ * X := by nlinarith
    have hxmul := mul_le_mul_of_nonneg_left hx.1 hδ.le
    nlinarith
  have hendpoint : 4 / (δ * x) ≤ 8 / H := by
    apply (div_le_div_iff₀ (mul_pos hδ hx0) hH0).mpr
    nlinarith
  have htriangle := norm_add_le
    (logarithmicWindowAverage f δ (Real.log x) -
      mellinPacket (Ioc K N) f
        (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
        (Real.log x + δ))
    (mellinPacket (Ioc K N) f
      (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
      (Real.log x + δ))
  rw [sub_add_cancel] at htriangle
  change ‖complexShortAverage f H x‖ ≤ _
  change ‖complexShortAverage f H x‖ ≤
    ‖logarithmicWindowAverage f δ (Real.log x)‖ + _ at hwindow
  dsimp only [δ] at hendpoint htriangle hwindow
  simp only [div_eq_mul_inv] at hwindow hendpoint happrox htriangle ⊢
  linarith only [hwindow, hendpoint, happrox, htriangle]

theorem shortAverage_le_mellinPacket (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {X H ε η x : ℝ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (hη : 0 < η) (hηhalf : η < 1/2)
    (hx : x ∈ Set.Icc X ((1 + ε) * X)) :
    let δ := Real.log ((X + H) / X)
    let hδ := (logarithmic_window_width hX (by linarith : 0 < H)).1
    ‖complexShortAverage f H x‖ ≤
      ‖mellinPacket (Ioc ⌊X⌋₊ ⌊(1 + ε) * (X + H)⌋₊) f
        (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
        (Real.log x + δ)‖ +
      (3 * ε + 11 / H + H / X + 1 / X + 16 * η) := by
  exact shortAverage_le_mellinPacket_of_support f hf hX hH hHX hη hηhalf hx le_rfl le_rfl

end JointDickman

end OAI
