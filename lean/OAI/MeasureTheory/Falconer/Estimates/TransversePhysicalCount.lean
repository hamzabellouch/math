import OAI.MeasureTheory.Falconer.Geometry.TripleFrameBound
import OAI.MeasureTheory.Falconer.Radial.PhysicalTubeCover

namespace OAI

/-! # The quantitative three-transverse-tube covering estimate -/

namespace Falconer
open Set Metric

theorem three_transverse_tube_cover (v : Fin 3 → Space 3)
    (hv : ∀ i, ‖v i‖ = 1) {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hgram : Δ ≤ Real.sqrt (tripleGram (v 0) (v 1) (v 2)))
    (E : Set (Space 3)) (A : Fin 3 → Finset (Space 3)) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hcover : ∀ i : Fin 3, ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (x-a)‖ ≤ C*δ) :
    ∃ P : Finset (Space 3), (∀ x ∈ E, ∃ p ∈ P, dist x p ≤ 5*δ) ∧
      (P.card:ℝ)^2 ≤ ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ)*((6*C+35)/Δ)^6 := by
  obtain ⟨e,_,haxis,he,hei⟩ := exists_transverse_triple_frame
    (le_of_eq (hv 0)) (le_of_eq (hv 1)) (le_of_eq (hv 2)) hΔ hgram
  have heq : ![v 0,v 1,v 2] = v := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at haxis
  let L := Nat.ceil (3*(C+5)/Δ+1/2)
  have hL : ‖e.symm.toContinuousLinearMap‖*(C+5)+1/2 ≤ (L:ℝ) := by
    apply le_trans _ (Nat.le_ceil _)
    have hh := mul_le_mul_of_nonneg_right hei (show 0 ≤ C+5 by linarith)
    calc
      _ ≤ (3/Δ)*(C+5)+1/2 := add_le_add_left hh _
      _ = _ := by ring
  have hsize : 2*(L:ℝ)+1 ≤ (6*C+35)/Δ := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 3*(C+5)/Δ+1/2 by positivity)
    change (L:ℝ) < 3*(C+5)/Δ+1/2+1 at hc
    have hm := mul_lt_mul_of_pos_right hc hΔ
    have hd : (3*(C+5)/Δ)*Δ = 3*(C+5) := div_mul_cancel₀ _ hΔ.ne'
    apply (le_div_iff₀ hΔ).mpr
    nlinarith
  obtain ⟨P,hP,hcard⟩ := physical_three_tube_cover e he v hv haxis E A R hE hδ L hL hcover
  refine ⟨P,hP,?_⟩
  exact hcard.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hsize 6) (by positivity))

end Falconer

end OAI
