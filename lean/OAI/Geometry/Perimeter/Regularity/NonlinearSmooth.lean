import OAI.Geometry.Perimeter.Regularity.LinearSchauder
import OAI.Geometry.Perimeter.Regularity.NonlinearLocalGain

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem nonlinear_geoC_all {θ δ K : ℝ}
    (hθ : 0<θ) (hθ' : θ ≤ 1/2) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    {G : Euc n → Euc n} (hG : ContDiff ℝ ∞ G)
    {f : Euc n → ℝ} {U : Set (Euc n)} (hU : IsOpen U)
    (hf : GeoC θ 1 f U) (heq : WeakFluxEquation (fun x ↦ G (gradient f x)) U)
    (hnear : ∀ p∈U, ‖ContinuousLinearMap.id ℝ (Euc n)-fderiv ℝ G (gradient f p)‖ < min δ (1/2)) :
    ∀ k : ℕ, GeoC θ (k+1) f U := by
  have hf2 := nonlinear_C2_gain hθ hθ' hK hc (hG.of_le (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hU hf heq hnear
  have hDG : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
  intro k
  induction k with
  | zero => exact hf
  | succ k ih =>
    have hgrad := ih.gradient hθ.le hU
    have hA := geoC_comp k hθ.le hU hgrad hDG
    refine ⟨hf.1,hf.2.1,fun e ↦ ?_⟩
    have hdir : ContDiffOn ℝ 1 (fun x ↦ fderiv ℝ f x e) U :=
      (hf2.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
    apply GeoC.local
    intro p hp
    obtain ⟨W,hW,hpW,hWU,hd⟩ := weak_nonlinear_derivative_local (hG.of_le (by simp)) hU hp hf2 heq e
    exact ⟨W,hW,hpW,linear_schauder k hθ hθ' hK hc hW (hA.mono hWU)
      (GeoC.const θ k 0 W) (hdir.mono hWU) hd (fun x hx ↦ hnear x (hWU hx))⟩

 theorem nonlinear_smooth {θ δ K : ℝ}
    (hθ : 0<θ) (hθ' : θ ≤ 1/2) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    {G : Euc n → Euc n} (hG : ContDiff ℝ ∞ G)
    {f : Euc n → ℝ} {U : Set (Euc n)} (hU : IsOpen U)
    (hf : GeoC θ 1 f U) (heq : WeakFluxEquation (fun x ↦ G (gradient f x)) U)
    (hnear : ∀ p∈U, ‖ContinuousLinearMap.id ℝ (Euc n)-fderiv ℝ G (gradient f p)‖ < min δ (1/2)) :
    ContDiffOn ℝ ∞ f U := by
  rw [contDiffOn_infty]
  intro k
  exact ((nonlinear_geoC_all hθ hθ' hK hc hG hU hf heq hnear k).mono_order).contDiff hU

end RPISingularHarnack

end

end OAI
