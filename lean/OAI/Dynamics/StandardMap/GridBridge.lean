import OAI.Dynamics.StandardMap.LocalSquareBridge

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def bridgeGridLo (i : Fin 32) : ℝ := (i:ℝ)/32
noncomputable def bridgeGridHi (i : Fin 32) : ℝ := ((i:ℝ)+1)/32
noncomputable def bridgeGridCell (i : Fin 32) : Set ℝ := Icc (bridgeGridLo i) (bridgeGridHi i)
lemma bridgeGrid_length (i : Fin 32) : bridgeGridHi i-bridgeGridLo i=1/32 := by
  unfold bridgeGridHi bridgeGridLo; ring
lemma bridgeGrid_order (i : Fin 32) : bridgeGridLo i ≤ bridgeGridHi i := by
  have := bridgeGrid_length i; linarith
lemma bridgeGrid_subset (i : Fin 32) : bridgeGridCell i ⊆ Icc (0:ℝ) 1 := by
  intro x hx
  have hi0 : (0:ℝ) ≤ i := by positivity
  have hi1 : (i:ℝ) < 32 := by exact_mod_cast i.isLt
  change (i:ℝ)/32 ≤ x ∧ x ≤ ((i:ℝ)+1)/32 at hx
  have hi2 : (i:ℝ) ≤ 31 := by exact_mod_cast (show (i:ℕ) ≤ 31 by omega)
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
lemma bridgeGrid_volume (i : Fin 32) : volume (bridgeGridCell i)=(1/32 : ℝ≥0∞) := by
  rw [bridgeGridCell,Real.volume_Icc,bridgeGrid_length,ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num
lemma bridgeGrid_cover (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : ∃ i : Fin 32, x ∈ bridgeGridCell i := by
  let q := ⌊32*x⌋₊
  have hq0 : (q:ℝ) ≤ 32*x := Nat.floor_le (by linarith [hx.1])
  have hq1 : 32*x < (q:ℝ)+1 := Nat.lt_floor_add_one _
  by_cases hq : q < 32
  · refine ⟨⟨q,hq⟩,?_⟩
    change (q:ℝ)/32 ≤ x ∧ x ≤ ((q:ℝ)+1)/32
    constructor <;> linarith
  · have hq2 : (32:ℝ) ≤ q := by exact_mod_cast (show 32 ≤ q by omega)
    refine ⟨31,?_⟩
    change (31:ℝ)/32 ≤ x ∧ x ≤ (31+1:ℝ)/32
    constructor <;> linarith [hx.2]
noncomputable def bridgeAreaScale : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.exp (-1152*Real.pi))*(1/32)) *
    (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(3/4))*(1/32))
noncomputable def bridgeLocalConstant : ℝ≥0∞ := ENNReal.ofReal (Real.exp (1152*Real.pi))*256
lemma bridgeAreaScale_pos : 0 < bridgeAreaScale := by
  unfold bridgeAreaScale
  have hs : (0:ℝ≥0∞) < 1/32 := by norm_num
  positivity
lemma bridgeAreaScale_ne_top : bridgeAreaScale ≠ ∞ := by
  unfold bridgeAreaScale
  finiteness
lemma bridgeLocalConstant_ne_top : bridgeLocalConstant ≠ ∞ := by
  unfold bridgeLocalConstant
  finiteness
lemma actual_grid_square_product (k : ℝ) (hc : BridgeScalarControl k)
    (np nm Bp Bm : ℕ) (hnp : 1 ≤ np) (hnm : 1 ≤ nm)
    (hBp : Bp=np ∨ Bp=np+1) (hBm : Bm=nm ∨ Bm=nm+1) (hBp2 : 2 ≤ Bp) (hBm2 : 2 ≤ Bm)
    (ix iy : Fin 32)
    (W H : Torus → ℝ) (hW : Continuous W) (hH : Continuous H) (hW0 : ∀ z, 0 ≤ W z)
    (h δ : ℝ) (hδ : 0 ≤ δ) (hδh : δ < h/2)
    (hWp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(Bm:ℤ)) z) (liftIter k (-(Bm:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bm-1:ℕ)) → |W (liftProjection z)-W (liftProjection w)| ≤ δ)
    (hHp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (Bp:ℤ) z) (liftIter k (Bp:ℤ) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bp-1:ℕ)) → |H (liftProjection z)-H (liftProjection w)| ≤ δ) :
    bridgeAreaScale *
      (∫⁻ z in {z : ℝ × ℝ | z ∈ bridgeGridCell ix ×ˢ bridgeGridCell iy ∧
        prefixEligible k Bp (np+1) z.swap ∧ prefixEligible k Bm (nm+1) z ∧ h < H (liftProjection z)},
        ENNReal.ofReal (W (liftProjection z))) ≤
    bridgeLocalConstant*((∫⁻ z, ENNReal.ofReal (W z) ∂area)+ENNReal.ofReal δ)*area {z | h/2 < H z} := by
  have hh := actual_local_square_product k hc np nm Bp Bm hnp hnm hBp hBm hBp2 hBm2
    (bridgeGridLo ix) (bridgeGridHi ix) (bridgeGridLo iy) (bridgeGridHi iy)
    (bridgeGrid_order iy) (by rw [bridgeGrid_length]; norm_num) (by rw [bridgeGrid_length]; norm_num)
    (bridgeGrid_subset ix) (bridgeGrid_subset iy) W H hW hH hW0 h δ hδ hδh hWp hHp
  change (ENNReal.ofReal (Real.exp (-1152*Real.pi))*volume (bridgeGridCell iy))*
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (bridgeGridCell ix))*_ ≤
    ENNReal.ofReal (Real.exp (1152*Real.pi))*(16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (bridgeGridCell ix))*
        ENNReal.ofReal δ*volume (bridgeGridCell iy))*(16*area {z | h/2 < H z}) at hh
  rw [bridgeGrid_volume,bridgeGrid_volume] at hh
  have hMp : 0 < growthBase k := by have := growthBase_ge_four k hc.nonneg; linarith
  have ha0 : 0 ≤ 24/growthBase k^((4/5:ℝ)) := by positivity
  have ha2 : (24/growthBase k^((4/5:ℝ)))^2 ≤ 1/4 := by nlinarith [hc.slope_small]
  have hl : Real.exp (-1152*Real.pi)*(3/4) ≤ Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hu : ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2)) ≤ 1 := by
    apply (ENNReal.ofReal_le_one).mpr
    have hc1 : Real.exp (-1152*Real.pi) ≤ 1 := Real.exp_le_one_iff.mpr (by have := Real.pi_pos; linarith)
    calc
      _ ≤ Real.exp (-1152*Real.pi)*1 := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (24/growthBase k^((4/5:ℝ)))]) (Real.exp_pos _).le
      _ ≤ 1 := by simpa using hc1
  have hs : (1/32:ℝ≥0∞) ≤ 1 := by norm_num
  apply le_trans (mul_le_mul_of_nonneg_right (show bridgeAreaScale ≤
      (ENNReal.ofReal (Real.exp (-1152*Real.pi))*(1/32))*
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*(1/32)) from by
        unfold bridgeAreaScale; gcongr) (by positivity))
  apply hh.trans
  have he : (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*(1/32))*
       ENNReal.ofReal δ*(1/32) ≤ ENNReal.ofReal δ := by
    calc
      _ ≤ (1*1)*ENNReal.ofReal δ*1 := by gcongr
      _ = _ := by simp
  calc
    _ ≤ ENNReal.ofReal (Real.exp (1152*Real.pi))*(16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+ENNReal.ofReal δ)*(16*area {z | h/2 < H z}) := by gcongr
    _ ≤ ENNReal.ofReal (Real.exp (1152*Real.pi))*(16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+16*ENNReal.ofReal δ)*(16*area {z | h/2 < H z}) := by gcongr; exact le_mul_of_one_le_left bot_le (by norm_num)
    _ = _ := by unfold bridgeLocalConstant; ring
end StandardMapEntropy

end OAI
