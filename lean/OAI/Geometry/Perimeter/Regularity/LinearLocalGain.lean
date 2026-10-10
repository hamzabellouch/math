import OAI.Geometry.Perimeter.Regularity.EllipticLocality
import OAI.Geometry.Perimeter.Regularity.LinearDerivativeGain

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem linear_directional_gain_local {θ δ K : ℝ}
    (hθ : 0<θ) (hθ' : θ ≤ 1/2) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    {A : Euc n → Euc n →L[ℝ] Euc n} {F : Euc n → Euc n}
    {f : Euc n → ℝ} {U : Set (Euc n)} (hU : IsOpen U) {p : Euc n} (hp : p∈U)
    (hA : GeoC θ 1 A U) (hF : GeoC θ 1 F U) (hf : GeoC θ 1 f U)
    (heq : WeakLinearEquation A f F U)
    (hnear : ‖ContinuousLinearMap.id ℝ (Euc n)-A p‖ < min δ (1/2)) (e : Euc n) :
    ∃ r : ℝ, 0<r ∧ Metric.ball p r⊆U ∧
      ContDiffOn ℝ 1 (fun x ↦ fderiv ℝ f x e) (Metric.ball p r) ∧
      GeometricHolderAt θ (gradient (fun x ↦ fderiv ℝ f x e)) p := by
  obtain ⟨W,hW,hpW,hWU,B,g,G,hB,hBc,hg,hgc,hG,hGc,heB,heg,heG⟩ :=
    local_compact_triple hU hp hA.1 hf.1 hF.1
  have he := (heq.mono hWU).congr hW heB.symm heg.symm heG.symm
  have hmf := (hf.gradient hθ.le hU).2 p hp
  have hmA := (hA.fderiv hθ.le hU).2 p hp
  have hmF := (hF.fderiv hθ.le hU).2 p hp
  have hmg := hmf.congr hθ.le (Filter.eventually_of_mem (hW.mem_nhds hpW)
    (fun x hx ↦ (gradient_eqOn hW heg hx).symm))
  have hmB := hmA.congr hθ.le (Filter.eventually_of_mem (hW.mem_nhds hpW)
    (fun x hx ↦ (fderiv_eqOn hW heB hx).symm))
  have hmG := hmF.congr hθ.le (Filter.eventually_of_mem (hW.mem_nhds hpW)
    (fun x hx ↦ (fderiv_eqOn hW heG hx).symm))
  obtain ⟨r,hr,hrW,hdr,hdm⟩ := linear_directional_gain hθ hθ' hK hc hB hBc hG hGc hg hgc
    hW hpW he hmg hmB hmG (by rwa [heB hpW]) e
  have hdEq : EqOn (fun x ↦ fderiv ℝ g x e) (fun x ↦ fderiv ℝ f x e) W :=
    fun x hx ↦ congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L e) (fderiv_eqOn hW heg hx)
  refine ⟨r,hr,hrW.trans hWU,hdr.congr (fun x hx ↦ (hdEq (hrW hx)).symm),?_⟩
  exact hdm.congr hθ.le (Filter.eventually_of_mem (hW.mem_nhds hpW)
    (fun x hx ↦ gradient_eqOn hW hdEq hx))

 theorem linear_C2_gain {θ δ K : ℝ}
    (hθ : 0<θ) (hθ' : θ ≤ 1/2) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    {A : Euc n → Euc n →L[ℝ] Euc n} {F : Euc n → Euc n}
    {f : Euc n → ℝ} {U : Set (Euc n)} (hU : IsOpen U)
    (hA : GeoC θ 1 A U) (hF : GeoC θ 1 F U) (hf : GeoC θ 1 f U)
    (heq : WeakLinearEquation A f F U)
    (hnear : ∀ p∈U, ‖ContinuousLinearMap.id ℝ (Euc n)-A p‖ < min δ (1/2)) :
    ContDiffOn ℝ 2 f U := by
  change ContDiffOn ℝ (1+1) f U
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨hf.1.differentiableOn one_ne_zero,by simp,contDiffOn_clm_apply.mpr (fun e p hp ↦ ?_)⟩
  obtain ⟨r,hr,hrU,hdr,hdm⟩ := linear_directional_gain_local hθ hθ' hK hc hU hp hA hF hf heq (hnear p hp) e
  exact (hdr.contDiffAt (Metric.ball_mem_nhds p hr)).contDiffWithinAt

end RPISingularHarnack

end

end OAI
