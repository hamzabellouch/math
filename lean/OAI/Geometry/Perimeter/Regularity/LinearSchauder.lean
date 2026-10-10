import OAI.Geometry.Perimeter.Regularity.LinearBaseGain
import OAI.Geometry.Perimeter.Regularity.LinearLocalGain
import OAI.Geometry.Perimeter.Regularity.LinearWeakDerivative

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem GeoC.of_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {θ : ℝ} {k l : ℕ} {f : Euc n → V} {U : Set (Euc n)}
    (h : GeoC θ k f U) (hl : l ≤ k) : GeoC θ l f U := by
  induction hl with
  | refl => exact h
  | @step k hk ih => exact ih h.mono_order

 theorem linear_schauder (k : ℕ) {θ δ K : ℝ}
    (hθ : 0<θ) (hθ' : θ ≤ 1/2) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    {A : Euc n → Euc n →L[ℝ] Euc n} {F : Euc n → Euc n}
    {f : Euc n → ℝ} {U : Set (Euc n)} (hU : IsOpen U)
    (hA : GeoC θ k A U) (hF : GeoC θ k F U) (hf : ContDiffOn ℝ 1 f U)
    (heq : WeakLinearEquation A f F U)
    (hnear : ∀ p∈U, ‖ContinuousLinearMap.id ℝ (Euc n)-A p‖ < min δ (1/2)) :
    GeoC θ (k+1) f U := by
  induction k generalizing A F f U with
  | zero => exact linear_geoC_one hθ hθ' hK hc hU hA hF hf heq hnear
  | succ k ih =>
    have hff := ih hU hA.mono_order hF.mono_order hf heq hnear
    have hA1 : GeoC θ 1 A U := hA.of_le (by omega)
    have hF1 : GeoC θ 1 F U := hF.of_le (by omega)
    have hf1 : GeoC θ 1 f U := hff.of_le (by omega)
    have hf2 := linear_C2_gain hθ hθ' hK hc hU hA1 hF1 hf1 heq hnear
    have hgrad := hff.gradient hθ.le hU
    refine ⟨hf,geoC_zero_of_C1 hθ.le hθ' hU hf,fun e ↦ ?_⟩
    have hforce : GeoC θ k (fun x ↦ fderiv ℝ F x e-fderiv ℝ A x e (gradient f x)) U :=
      (hF.2.2 e).sub hθ.le hU ((hA.2.2 e).clm_apply hθ.le hU hgrad)
    have hdir : ContDiffOn ℝ 1 (fun x ↦ fderiv ℝ f x e) U :=
      (hf2.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
    apply GeoC.local
    intro p hp
    obtain ⟨W,hW,hpW,hWU,hd⟩ := weak_linear_derivative_local hU hp hA1.1 hF1.1 hf2 heq e
    exact ⟨W,hW,hpW,ih hW (hA.mono_order.mono hWU) (hforce.mono hWU) (hdir.mono hWU)
      hd (fun x hx ↦ hnear x (hWU hx))⟩

end RPISingularHarnack

end

end OAI
