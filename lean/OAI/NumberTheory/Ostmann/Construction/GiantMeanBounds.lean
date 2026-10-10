import OAI.NumberTheory.Ostmann.Construction.GiantMean

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
variable {p : ℕ} [NeZero p]

theorem giantTestReal_support_mean (S : Finset (ZMod p))
    (hpos : 0 < Supply.density S) (hlt : Supply.density S < 1) :
    (∑ x ∈ S, giantTestReal S x)/(S.card : ℝ) =
      (Real.sqrt (Supply.density S*(1-Supply.density S))/Supply.density S) *
        Supply.gamma S := by
  have hp : (0:ℝ)<p := by exact_mod_cast NeZero.pos p
  have hc : (0:ℝ)<S.card := by
    have h := hpos
    dsimp [Supply.density] at h
    rw [ZMod.card] at h
    exact (div_pos_iff_of_pos_right hp).mp h
  rw [giantTestReal_sum_support S hpos hlt]
  dsimp [Supply.density, Supply.gamma]
  rw [ZMod.card]
  field_simp

theorem giantTestReal_support_mean_lower (S : Finset (ZMod p)) {δ : ℝ}
    (hδ : 0 ≤ δ) (hlo : (1:ℝ)/3 ≤ Supply.density S)
    (hhi : Supply.density S ≤ (2:ℝ)/3) (hgamma : δ ≤ Supply.gamma S) :
    δ/Real.sqrt 2 ≤ (∑ x ∈ S, giantTestReal S x)/(S.card : ℝ) := by
  have hpos : 0 < Supply.density S := by linarith
  have hlt : Supply.density S < 1 := by linarith
  rw [giantTestReal_support_mean S hpos hlt]
  let σ := Supply.density S
  have hvar : σ^2/2 ≤ σ*(1-σ) := by dsimp [σ]; nlinarith
  have hlower := Real.sqrt_le_sqrt hvar
  rw [Real.sqrt_div (sq_nonneg σ), Real.sqrt_sq hpos.le] at hlower
  have hquot : 1/Real.sqrt 2 ≤ Real.sqrt (σ*(1-σ))/σ := by
    apply (le_div_iff₀ hpos).mpr
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hlower
  have hquotnonneg : 0 ≤ Real.sqrt (σ*(1-σ))/σ :=
    div_nonneg (Real.sqrt_nonneg _) hpos.le
  calc
    δ/Real.sqrt 2 = (1/Real.sqrt 2)*δ := by ring
    _ ≤ (Real.sqrt (σ*(1-σ))/σ)*δ := mul_le_mul_of_nonneg_right hquot hδ
    _ ≤ (Real.sqrt (σ*(1-σ))/σ)*Supply.gamma S :=
      mul_le_mul_of_nonneg_left hgamma hquotnonneg

end Ostmann.Construction

end

end OAI
