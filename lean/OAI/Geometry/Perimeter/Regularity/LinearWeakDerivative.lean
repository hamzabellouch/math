import OAI.Geometry.Perimeter.Regularity.EllipticLocality
import OAI.Geometry.Perimeter.Regularity.WeakDerivative

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem weak_linear_derivative {A : Euc n → Euc n →L[ℝ] Euc n}
    {F : Euc n → Euc n} {f : Euc n → ℝ} {U : Set (Euc n)}
    (hA : ContDiff ℝ 1 A) (hF : ContDiff ℝ 1 F) (hf : ContDiff ℝ 2 f)
    (h : WeakLinearEquation A f F U) (e : Euc n) :
    WeakLinearEquation A (fun x ↦ fderiv ℝ f x e)
      (fun x ↦ fderiv ℝ F x e-fderiv ℝ A x e (gradient f x)) U := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ (Euc n)).symm.toContinuousLinearMap.contDiff.comp hdf
  have hV : ContDiff ℝ 1 (fun x ↦ A x (gradient f x)-F x) := (hA.clm_apply hg).sub hF
  have hd := ((weakLinear_iff_flux hA.continuous (hf.of_le (by norm_num)) hF.continuous).mp h).derivative hV e
  have hdir : ContDiff ℝ 1 (fun x ↦ fderiv ℝ f x e) := hdf.clm_apply contDiff_const
  have hH : Continuous (fun x ↦ fderiv ℝ F x e-fderiv ℝ A x e (gradient f x)) :=
    ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).sub
      (((hA.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply hg.continuous)
  apply (weakLinear_iff_flux hA.continuous hdir hH).mpr
  apply hd.congr
  intro x hx
  have hr := (((hA.differentiable (by simp) x).hasFDerivAt.clm_apply
    (hg.differentiable (by simp) x).hasFDerivAt).sub (hF.differentiable (by simp) x).hasFDerivAt).fderiv
  have he := congrArg (fun L : Euc n →L[ℝ] Euc n ↦ L e) hr
  dsimp only at *
  change fderiv ℝ (fun y ↦ A y (gradient f y)-F y) x e = _ at he
  rw [he,gradient_direction_swap hf]
  simp only [sub_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  module

 theorem weak_linear_derivative_local {A : Euc n → Euc n →L[ℝ] Euc n}
    {F : Euc n → Euc n} {f : Euc n → ℝ} {U : Set (Euc n)}
    (hU : IsOpen U) {p : Euc n} (hp : p∈U)
    (hA : ContDiffOn ℝ 1 A U) (hF : ContDiffOn ℝ 1 F U) (hf : ContDiffOn ℝ 2 f U)
    (h : WeakLinearEquation A f F U) (e : Euc n) :
    ∃ W : Set (Euc n), IsOpen W ∧ p∈W ∧ W⊆U ∧
      WeakLinearEquation A (fun x ↦ fderiv ℝ f x e)
        (fun x ↦ fderiv ℝ F x e-fderiv ℝ A x e (gradient f x)) W := by
  obtain ⟨W,hW,hpW,hWU,B,g,G,hB,hBc,hg,hgc,hG,hGc,heB,heg,heG⟩ :=
    local_compact_triple hU hp hA hf hF
  have he := (h.mono hWU).congr hW heB.symm heg.symm heG.symm
  have hd := weak_linear_derivative hB hG hg he e
  refine ⟨W,hW,hpW,hWU,hd.congr hW heB ?_ ?_⟩
  · intro x hx
    dsimp only
    rw [fderiv_eqOn hW heg hx]
  · intro x hx
    dsimp only
    rw [fderiv_eqOn hW heG hx,fderiv_eqOn hW heB hx,gradient_eqOn hW heg hx]

end RPISingularHarnack

end

end OAI
