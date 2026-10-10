import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceConfigurations
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Filter InitialCharacterScale

def configurationListLengthBound (k : ℕ) : ℕ :=
  ⌈2 * Real.exp (2*(k : ℝ)/10000)⌉₊

def configurationIndexExponent (k : ℕ) : ℕ :=
  (k+1)*(configurationListLengthBound k+1)+2*k

def configurationLossCoefficient (β : ℝ) : ℝ := 2*(|β|+1)

theorem configurationLossCoefficient_pos (β : ℝ) : 0 < configurationLossCoefficient β := by
  unfold configurationLossCoefficient
  positivity

theorem configurationListLengthBound_lower (k : ℕ) :
    2 * Real.exp (2*(k : ℝ)/10000) ≤ (configurationListLengthBound k : ℝ) :=
  Nat.le_ceil _

theorem configurationIndexExponent_le (k : ℕ) :
    (configurationIndexExponent k : ℝ) ≤ 2 * maxCells 4 k := by
  have hn := (Nat.ceil_lt_add_one
    (by positivity : 0 ≤ 2 * Real.exp (2*(k : ℝ)/10000))).le
  change (configurationListLengthBound k : ℝ) ≤
    2 * Real.exp (2*(k : ℝ)/10000)+1 at hn
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have he : 1 ≤ Real.exp (2*(k : ℝ)/10000) := Real.one_le_exp_iff.mpr (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (k : ℝ)+1)
  have hek := mul_le_mul_of_nonneg_left he hk
  unfold configurationIndexExponent maxCells
  have hex : (2/10000 : ℝ)*(k : ℝ) = 2*(k : ℝ)/10000 := by ring
  rw [hex]
  push_cast
  nlinarith

theorem configuration_exponent_cost_le (β : ℝ) (k : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    configurationCountCoefficient β * (configurationIndexExponent k : ℝ) * L ≤
      configurationLossCoefficient β * maxCells 4 k * L := by
  have hh := mul_le_mul_of_nonneg_left (configurationIndexExponent_le k)
    (configurationCountCoefficient_pos β).le
  have hh' := mul_le_mul_of_nonneg_right hh hL
  convert hh' using 1
  unfold configurationCountCoefficient configurationLossCoefficient
  ring

theorem retained_card_lower (β : ℝ) (k : ℕ) (L X Cw m : ℝ)
    (hL : 0 ≤ L) (hX : 0 < X) (H H0 : ℕ)
    (hH : Real.sqrt X * Real.exp (-Cw*m) ≤ (H : ℝ))
    (hcount : (H : ℝ) ≤
      Real.exp (configurationCountCoefficient β * (configurationIndexExponent k : ℝ) * L) * H0) :
    Real.exp (-Cw*m - configurationLossCoefficient β * maxCells 4 k * L) ≤
      (H0 : ℝ) / Real.sqrt X := by
  let A := configurationCountCoefficient β * (configurationIndexExponent k : ℝ) * L
  let B := configurationLossCoefficient β * maxCells 4 k * L
  have hAB : A ≤ B := configuration_exponent_cost_le β k hL
  have hmain : Real.sqrt X * Real.exp (-Cw*m) ≤ Real.exp A * H0 := hH.trans hcount
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hX)).mpr
  change Real.exp (-Cw*m-B) * Real.sqrt X ≤ (H0 : ℝ)
  calc
    _ = Real.exp (-B) * (Real.sqrt X * Real.exp (-Cw*m)) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ Real.exp (-B) * (Real.exp A * (H0 : ℝ)) :=
      mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
    _ = Real.exp (A-B) * (H0 : ℝ) := by
      rw [Real.exp_sub, Real.exp_neg]
      ring
    _ ≤ 1 * (H0 : ℝ) := mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.mpr (by linarith)) (Nat.cast_nonneg _)
    _ = _ := one_mul _

theorem eventually_fixed_source_configuration_retained (β : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ {α : Type*} [DecidableEq α] (k : ℕ)
      (H : Finset α) (f : α → SourceConfiguration k),
      (∀ x ∈ H, (f x).Bounded ⌊Real.exp (β*L)⌋₊ (configurationListLengthBound k)) →
      ∀ X Cw m : ℝ, 0 < X →
      Real.sqrt X * Real.exp (-Cw*m) ≤ (H.card : ℝ) →
      ∃ cfg : SourceConfiguration k, ∃ H0 : Finset α,
        cfg.Bounded ⌊Real.exp (β*L)⌋₊ (configurationListLengthBound k) ∧
        H0 ⊆ H ∧ (∀ x ∈ H0, f x = cfg) ∧
        Real.exp (-Cw*m - configurationLossCoefficient β * maxCells 4 k * L) ≤
          (H0.card : ℝ) / Real.sqrt X := by
  filter_upwards [eventually_fixed_source_configuration β, eventually_ge_atTop (0 : ℝ)] with L hfix hL
  intro α inst k H f hf X Cw m hX hH
  obtain ⟨cfg,H0,hb,hs,he,hc⟩ := hfix k (configurationListLengthBound k) H f hf
  refine ⟨cfg,H0,hb,hs,he,retained_card_lower β k L X Cw m hL hX H.card H0.card hH ?_⟩
  simpa only [configurationIndexExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hc

end Ostmann.Characters.HigherBiasSource

end

end OAI
