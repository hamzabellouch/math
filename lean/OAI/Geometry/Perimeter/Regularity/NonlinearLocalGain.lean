import OAI.Geometry.Perimeter.Regularity.NonlinearDerivativeGain
import OAI.Geometry.Perimeter.Regularity.EllipticLocality
import OAI.Geometry.Perimeter.Regularity.WeakDerivative

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem nonlinear_C2_gain {θ δ K : ℝ}
    (hθ : 0<θ) (hθ' : θ ≤ 1/2) (hK : 1 ≤ K)
    (hc : LinearContractionProperty n θ δ K)
    {G : Euc n → Euc n} (hG : ContDiff ℝ 2 G)
    {f : Euc n → ℝ} {U : Set (Euc n)} (hU : IsOpen U)
    (hf : GeoC θ 1 f U) (heq : WeakFluxEquation (fun x ↦ G (gradient f x)) U)
    (hnear : ∀ p∈U, ‖ContinuousLinearMap.id ℝ (Euc n)-fderiv ℝ G (gradient f p)‖ < min δ (1/2)) :
    ContDiffOn ℝ 2 f U := by
  have hθ1 : θ<1 := by linarith
  change ContDiffOn ℝ (1+1) f U
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨hf.1.differentiableOn one_ne_zero,by simp,contDiffOn_clm_apply.mpr (fun e p hp ↦ ?_)⟩
  obtain ⟨a,ha,haU,g,hg,hgc,heg⟩ := local_compact_extension hU hp hf.1
  let W := Metric.ball p (2*a)
  have hW : IsOpen W := Metric.isOpen_ball
  have hpW : p∈W := Metric.mem_ball_self (by positivity)
  have hWU : W⊆U := Metric.ball_subset_closedBall.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans haU)
  have heGrad : EqOn (gradient g) (gradient f) W := gradient_eqOn hW heg
  have he := (heq.mono hWU).congr (fun x hx ↦ congrArg G (heGrad hx).symm)
  have hm := ((hf.gradient hθ.le hU).2 p hp).congr hθ.le
    (Filter.eventually_of_mem (hW.mem_nhds hpW) (fun x hx ↦ (heGrad hx).symm))
  obtain ⟨r,hr,hrW,hdr,hdm⟩ := nonlinear_directional_gain hθ hθ1 hK hc hG hg hgc hW hpW he hm
    (by rw [heGrad hpW]; exact hnear p hp) e
  have hdEq : EqOn (fun x ↦ fderiv ℝ g x e) (fun x ↦ fderiv ℝ f x e) W :=
    fun x hx ↦ congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L e) (fderiv_eqOn hW heg hx)
  exact ((hdr.congr (fun x hx ↦ (hdEq (hrW hx)).symm)).contDiffAt
    (Metric.ball_mem_nhds p hr)).contDiffWithinAt

 theorem weak_nonlinear_derivative {G : Euc n → Euc n} (hG : ContDiff ℝ 1 G)
    {f : Euc n → ℝ} (hf : ContDiff ℝ 2 f) {U : Set (Euc n)}
    (h : WeakFluxEquation (fun x ↦ G (gradient f x)) U) (e : Euc n) :
    WeakLinearEquation (fun x ↦ fderiv ℝ G (gradient f x))
      (fun x ↦ fderiv ℝ f x e) (fun _ ↦ 0) U := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ (Euc n)).symm.toContinuousLinearMap.contDiff.comp hdf
  have hd := h.derivative (hG.comp hg) e
  have he : EqOn (fun x ↦ fderiv ℝ (fun y ↦ G (gradient f y)) x e)
      (fun x ↦ fderiv ℝ G (gradient f x) (gradient (fun y ↦ fderiv ℝ f y e) x)) U := by
    intro x hx
    dsimp only
    rw [gradient_direction_swap hf]
    exact congrArg (fun L : Euc n →L[ℝ] Euc n ↦ L e)
      (((hG.differentiable (by simp) (gradient f x)).hasFDerivAt.comp x
        (hg.differentiable (by simp) x).hasFDerivAt).fderiv)
  intro φ
  simpa only [inner_zero_left,integral_zero] using hd.congr he φ

 theorem weak_nonlinear_derivative_local {G : Euc n → Euc n} (hG : ContDiff ℝ 1 G)
    {f : Euc n → ℝ} {U : Set (Euc n)} (hU : IsOpen U) {p : Euc n} (hp : p∈U)
    (hf : ContDiffOn ℝ 2 f U)
    (h : WeakFluxEquation (fun x ↦ G (gradient f x)) U) (e : Euc n) :
    ∃ W : Set (Euc n), IsOpen W ∧ p∈W ∧ W⊆U ∧
      WeakLinearEquation (fun x ↦ fderiv ℝ G (gradient f x))
        (fun x ↦ fderiv ℝ f x e) (fun _ ↦ 0) W := by
  obtain ⟨a,ha,haU,g,hg,hgc,heg⟩ := local_compact_extension hU hp hf
  let W := Metric.ball p (2*a)
  have hW : IsOpen W := Metric.isOpen_ball
  have hpW : p∈W := Metric.mem_ball_self (by positivity)
  have hWU : W⊆U := Metric.ball_subset_closedBall.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans haU)
  have heGrad : EqOn (gradient g) (gradient f) W := gradient_eqOn hW heg
  have he := (h.mono hWU).congr (fun x hx ↦ congrArg G (heGrad hx).symm)
  have hd := weak_nonlinear_derivative hG hg he e
  refine ⟨W,hW,hpW,hWU,hd.congr hW ?_ ?_ (fun _ _ ↦ rfl)⟩
  · intro x hx
    dsimp only
    rw [heGrad hx]
  · intro x hx
    dsimp only
    rw [fderiv_eqOn hW heg hx]

end RPISingularHarnack

end

end OAI
