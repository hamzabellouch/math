import OAI.MeasureTheory.Falconer.Geometry.GeneralFrameBound
import OAI.MeasureTheory.Falconer.Radial.GeneralPhysicalTubeCover

namespace OAI

/-! # Quantitative general-dimensional transverse tube counting -/

namespace Falconer
open Set Metric
open scoped BigOperators
variable {n : ℕ}

noncomputable def generalTubeCountConstant (d : ℕ) (C : ℝ) : ℝ :=
  2*(d:ℝ)^2*(d.factorial:ℝ)*(C+(d:ℝ)^2)+4

theorem general_transverse_tube_cover (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (v : Fin (n+1) → Space (n+1)) (hv : ∀ i, ‖v i‖ = 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hgram : Δ ≤ Real.sqrt (Matrix.gram ℝ v).det)
    (E : Set (Space (n+1))) (A : Fin (n+1) → Finset (Space (n+1))) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hcover : ∀ i : Fin (n+1), ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (x-a)‖ ≤ C*δ) :
    ∃ P : Finset (Space (n+1)),
      (∀ x ∈ E, ∃ p ∈ P, dist x p ≤ ((n+1:ℕ):ℝ)^2*δ) ∧
      (P.card:ℝ)^n ≤ (∏ i : Fin (n+1), ((A i).card:ℝ))*
        (generalTubeCountConstant (n+1) C/Δ)^(n*(n+1)) := by
  obtain ⟨e,_,haxis,he,hei⟩ := exists_general_transverse_frame v (fun i => (hv i).le) hΔ hgram
  let D : ℝ := ((n+1:ℕ):ℝ)^2*((n+1).factorial:ℝ)
  let L := Nat.ceil (D*(C+((n+1:ℕ):ℝ)^2)/Δ+1/2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCd : 0 ≤ C+((n+1:ℕ):ℝ)^2 := by positivity
  have hL : ‖e.symm.toContinuousLinearMap‖*(C+((n+1:ℕ):ℝ)^2)+1/2 ≤ (L:ℝ) := by
    apply le_trans _ (Nat.le_ceil _)
    have hh := mul_le_mul_of_nonneg_right hei hCd
    calc
      _ ≤ (D/Δ)*(C+((n+1:ℕ):ℝ)^2)+1/2 := add_le_add hh le_rfl
      _ = _ := by ring
  have hsize : 2*(L:ℝ)+1 ≤ generalTubeCountConstant (n+1) C/Δ := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ D*(C+((n+1:ℕ):ℝ)^2)/Δ+1/2 by positivity)
    change (L:ℝ) < D*(C+((n+1:ℕ):ℝ)^2)/Δ+1/2+1 at hc
    have hm := mul_lt_mul_of_pos_right hc hΔ
    have hd : (D*(C+((n+1:ℕ):ℝ)^2)/Δ)*Δ = D*(C+((n+1:ℕ):ℝ)^2) := div_mul_cancel₀ _ hΔ.ne'
    apply (le_div_iff₀ hΔ).mpr
    have hconst : generalTubeCountConstant (n+1) C =
        2*D*(C+((n+1:ℕ):ℝ)^2)+4 := by
      unfold generalTubeCountConstant D
      ring
    rw [hconst]
    nlinarith
  obtain ⟨P,hP,hcard⟩ := general_physical_tube_cover hLW hn e he v hv haxis E A R hE hδ L hL hcover
  have hreal : (P.card:ℝ)^n ≤ (∏ i : Fin (n+1), ((A i).card:ℝ))*(2*(L:ℝ)+1)^(n*(n+1)) := by
    exact_mod_cast hcard
  have hb : 0 ≤ 2*(L:ℝ)+1 := by positivity
  have hp : 0 ≤ ∏ i : Fin (n+1), ((A i).card:ℝ) :=
    Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  exact ⟨P,hP,hreal.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hb hsize _) hp)⟩

end Falconer

end OAI
