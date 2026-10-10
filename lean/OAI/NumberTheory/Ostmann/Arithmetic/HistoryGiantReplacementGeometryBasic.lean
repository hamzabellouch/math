import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudgetPrime

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantReplacementGeometry
open ScaleBudget PrimeCellActualErrorBudget Filter

structure GeometryBounds (d L₀ G : ℝ) (M : ℕ) (L : ℝ) : Prop where
  lower_scale : Real.exp (giant.a₀*L) ≤ G-1
  modulus_lt_cell : (M:ℝ) < Real.exp (G-1)
  lower_threshold : L₀ ≤ G-1
  modulus_admissible : (M:ℝ) ≤ Real.exp (d*(G-1)^(1/3:ℝ))

theorem eventually_geometryBounds {d : ℝ} (hd : 0<d) (L₀ : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (block G : ℝ) (M : ℕ),
      Real.exp ((1/20:ℝ)*L) ≤ block → block-2 < G → 0<M →
      Real.log (M:ℝ) ≤ Real.exp (giant.μ*L) → GeometryBounds d L₀ G M L := by
  have hscale := eventually_poly_exp_le 1 0
    (by norm_num [giant] : giant.a₀ < (1/20:ℝ)) (by norm_num : (0:ℝ)<1/2)
  have hmargin := eventually_poly_exp_le 3 0
    (by norm_num : (0:ℝ)<1/20) (by norm_num : (0:ℝ)<1/2)
  have hthreshold := eventually_poly_exp_le L₀ 0
    (by norm_num [giant] : (0:ℝ)<giant.a₀) (by norm_num : (0:ℝ)<1)
  filter_upwards [hscale,hmargin,hthreshold,eventually_modulus_admissible giant hd,
    eventually_ge_atTop (1:ℝ)] with L hs hm ht hap hL
  simp only [pow_zero,mul_one,one_mul,zero_mul,Real.exp_zero] at hs hm ht
  intro block G M hb hG hM hmod
  have hlo : Real.exp (giant.a₀*L) ≤ G-1 := by linarith
  have hgap : giant.μ*L < giant.a₀*L := by
    exact mul_lt_mul_of_pos_right (by norm_num [giant]) (by linarith)
  have hlog : Real.log (M:ℝ) < G-1 :=
    lt_of_le_of_lt hmod ((Real.exp_lt_exp.mpr hgap).trans_le hlo)
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  refine ⟨hlo,?_,ht.trans hlo,hap M (G-1) hM hmod hlo⟩
  simpa only [Real.exp_log hMp] using Real.exp_lt_exp.mpr hlog

theorem GeometryBounds.at_lower {d L₀ G L lower : ℝ} {M : ℕ}
    (h : GeometryBounds d L₀ G M L) (hd : 0 ≤ d) (hlower : G-1 ≤ lower) :
    Real.exp (giant.a₀*L) ≤ lower ∧ (M:ℝ) < Real.exp lower ∧
      L₀ ≤ lower ∧ (M:ℝ) ≤ Real.exp (d*lower^(1/3:ℝ)) := by
  refine ⟨h.lower_scale.trans hlower,
    h.modulus_lt_cell.trans_le (Real.exp_le_exp.mpr hlower),
    h.lower_threshold.trans hlower,?_⟩
  apply h.modulus_admissible.trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hd
  exact Real.rpow_le_rpow ((Real.exp_pos _).le.trans h.lower_scale)
    hlower (by norm_num : (0:ℝ)≤1/3)

end Ostmann.Arithmetic.HistoryGiantReplacementGeometry

end

end OAI
