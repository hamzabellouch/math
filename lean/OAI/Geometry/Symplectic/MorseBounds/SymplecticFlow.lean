import OAI.Geometry.Symplectic.MorseBounds.ManifoldFlow
import OAI.Geometry.Symplectic.MorseBounds.Cotangent

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.SymplecticFlow
open Filter Set
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev TwoForm := E →L[ℝ] E →L[ℝ] ℝ

lemma alternating_skew (w : TwoForm (E := E)) (h : ∀ u, w u u = 0) (u v : E) :
    w u v = -w v u := by
  have hh := h (u + v)
  simp only [map_add, add_apply, h u, h v, zero_add, add_zero] at hh
  linarith

lemma derivative_alt (w : E → TwoForm (E := E)) (hw : ContDiff ℝ ∞ w)
    (halt : ∀ x u, w x u u = 0) (x z u : E) : fderiv ℝ w x z u u = 0 := by
  let A : TwoForm (E := E) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ u).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u)
  have h := A.hasFDerivAt.comp x ((hw.differentiable (by simp) x).hasFDerivAt)
  have he : (fun y => A (w y)) = fun _ : E => (0 : ℝ) := funext (fun y => halt y u)
  have hh := h.fderiv
  change fderiv ℝ (fun y => A (w y)) x = A.comp (fderiv ℝ w x) at hh
  rw [he] at hh
  simp only [fderiv_fun_const] at hh
  exact (congrArg (fun f : E →L[ℝ] ℝ => f z) hh).symm

theorem infinitesimal_preservation
    (w : E → TwoForm (E := E)) (V : E → E) (H : E → ℝ)
    (hw : ContDiff ℝ ∞ w) (hV : ContDiff ℝ ∞ V) (hH : ContDiff ℝ ∞ H)
    (halt : ∀ x u, w x u u = 0)
    (hclosed : ∀ x u v z, fderiv ℝ w x u v z +
      fderiv ℝ w x v z u + fderiv ℝ w x z u v = 0)
    (hham : ∀ x u, w x (V x) u = fderiv ℝ H x u) (x u v : E) :
    fderiv ℝ w x (V x) u v + w x (fderiv ℝ V x u) v +
      w x u (fderiv ℝ V x v) = 0 := by
  have hdw := (hw.differentiable (by simp) x).hasFDerivAt
  have hdV := (hV.differentiable (by simp) x).hasFDerivAt
  have ham : (fun y => w y (V y)) = fderiv ℝ H := by
    funext y; ext a; exact hham y a
  have hd := hdw.clm_apply hdV
  have hderiv := hd.fderiv
  change fderiv ℝ (fun y => w y (V y)) x = _ at hderiv
  rw [ham] at hderiv
  have hu := congrArg (fun f : E →L[ℝ] E →L[ℝ] ℝ => f u v) hderiv
  have hv := congrArg (fun f : E →L[ℝ] E →L[ℝ] ℝ => f v u) hderiv
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at hu hv
  have hs := (hH.contDiffAt (x := x)).isSymmSndFDerivAt (show minSmoothness ℝ 2 ≤ ∞ by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  have hc := hclosed x (V x) u v
  have ha := alternating_skew (w x) (halt x) u (fderiv ℝ V x v)
  have hdu := alternating_skew (fderiv ℝ w x u) (derivative_alt w hw halt x u) (V x) v
  have hdv := alternating_skew (fderiv ℝ w x v) (derivative_alt w hw halt x v) u (V x)
  have hsym : fderiv ℝ (fderiv ℝ H) x u v = fderiv ℝ (fderiv ℝ H) x v u := hs u v
  linarith

lemma variational_derivative (V : E → E) (Phi : ℝ × E → E)
    (hV : ContDiff ℝ ∞ V) (hPhi : ContDiff ℝ ∞ Phi)
    (hODE : ∀ t x, HasDerivAt (fun s => Phi (s,x)) (V (Phi (t,x))) t)
    (t : ℝ) (x : E) :
    HasDerivAt (fun s => fderiv ℝ (fun y => Phi (s,y)) x)
      ((fderiv ℝ V (Phi (t,x))).comp (fderiv ℝ (fun y => Phi (t,y)) x)) t := by
  let D := fderiv ℝ Phi
  let A := fderiv ℝ D (t,x)
  let L : ((ℝ × E) →L[ℝ] E) →L[ℝ] E →L[ℝ] E :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip (ContinuousLinearMap.inr ℝ ℝ E)
  let T : ((ℝ × E) →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E (1,0)
  have hD : ContDiff ℝ 1 D := hPhi.fderiv_right (by
    change (2 : ℕ∞ω) ≤ ∞
    exact WithTop.coe_le_coe.mpr le_top)
  have hd (s : ℝ) (y : E) := hPhi.differentiable (by simp) (s,y)
  have ht : (fun s => fderiv ℝ (fun y => Phi (s,y)) x) = fun s => L (D (s,x)) := by
    funext s
    exact ((hd s x).hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)).fderiv
  have hB : (fun y => T (D (t,y))) = fun y => V (Phi (t,y)) := by
    funext y
    have h := ((hd t y).hasFDerivAt.comp t (hasFDerivAt_prodMk_left t y)).hasDerivAt
    exact h.unique (hODE t y)
  have hd1 := (T.hasFDerivAt.comp (t,x) (hD.differentiable (by simp) (t,x)).hasFDerivAt).comp x
    (hasFDerivAt_prodMk_right t x)
  have hder : (T.comp A).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      (fderiv ℝ V (Phi (t,x))).comp (fderiv ℝ (fun y => Phi (t,y)) x) := by
    change HasFDerivAt (fun y => T (D (t,y))) _ x at hd1
    rw [hB] at hd1
    exact hd1.unique ((hV.differentiable (by simp) (Phi (t,x))).hasFDerivAt.comp x
      (((hd t x).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).differentiableAt.hasFDerivAt))
  have hJ := L.hasFDerivAt.comp_hasDerivAt t
    (((hD.differentiable (by simp) (t,x)).hasFDerivAt.comp t
      (hasFDerivAt_prodMk_left t x)).hasDerivAt)
  have hsym := (hPhi.contDiffAt (x := (t,x))).isSymmSndFDerivAt
    (show minSmoothness ℝ 2 ≤ ∞ by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
  have heq : L (A (1,0)) = (fderiv ℝ V (Phi (t,x))).comp
      (fderiv ℝ (fun y => Phi (t,y)) x) := by
    rw [← hder]
    ext v
    exact hsym (1,0) (0,v)
  rw [ht]
  change HasDerivAt (fun s => L (D (s,x))) (L (A (1,0))) t at hJ
  rwa [heq] at hJ

lemma derivative_altAt (w : E → TwoForm (E := E)) (x : E)
    (hw : DifferentiableAt ℝ w x)
    (halt : ∀ᶠ y in 𝓝 x, ∀ u, w y u u = 0) (z u : E) :
    fderiv ℝ w x z u u = 0 := by
  let A : TwoForm (E := E) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ u).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u)
  have h := HasFDerivAt.comp (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (G := ℝ) x A.hasFDerivAt hw.hasFDerivAt
  have he : (fun _ : E => (0 : ℝ)) =ᶠ[𝓝 x] fun y => A (w y) := by
    filter_upwards [halt] with y hy
    exact (hy u).symm
  have hh := (h.congr_of_eventuallyEq he).fderiv
  simp only [fderiv_fun_const] at hh
  exact (congrArg (fun f : E →L[ℝ] ℝ => f z) hh).symm

theorem infinitesimal_preservationAt
    (w : E → TwoForm (E := E)) (V : E → E) (H : E → ℝ) (x : E)
    (hw : DifferentiableAt ℝ w x) (hV : DifferentiableAt ℝ V x)
    (hH : ContDiffAt ℝ ∞ H x)
    (halt : ∀ᶠ y in 𝓝 x, ∀ u, w y u u = 0)
    (hclosed : ∀ u v z, fderiv ℝ w x u v z +
      fderiv ℝ w x v z u + fderiv ℝ w x z u v = 0)
    (hham : ∀ᶠ y in 𝓝 x, ∀ u, w y (V y) u = fderiv ℝ H y u) (u v : E) :
    fderiv ℝ w x (V x) u v + w x (fderiv ℝ V x u) v +
      w x u (fderiv ℝ V x v) = 0 := by
  have ham : fderiv ℝ H =ᶠ[𝓝 x] fun y => w y (V y) := by
    filter_upwards [hham] with y hy
    ext a
    exact (hy a).symm
  have hderiv := ((hw.hasFDerivAt.clm_apply hV.hasFDerivAt).congr_of_eventuallyEq ham).fderiv
  have hu := congrArg (fun f : E →L[ℝ] E →L[ℝ] ℝ => f u v) hderiv
  have hv := congrArg (fun f : E →L[ℝ] E →L[ℝ] ℝ => f v u) hderiv
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at hu hv
  have hs := hH.isSymmSndFDerivAt (show minSmoothness ℝ 2 ≤ ∞ by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  have hc := hclosed (V x) u v
  have ha := alternating_skew (w x) (halt.self_of_nhds) u (fderiv ℝ V x v)
  have hdu := alternating_skew (fderiv ℝ w x u) (derivative_altAt w x hw halt u) (V x) v
  have hdv := alternating_skew (fderiv ℝ w x v) (derivative_altAt w x hw halt v) u (V x)
  have hsym : fderiv ℝ (fderiv ℝ H) x u v = fderiv ℝ (fderiv ℝ H) x v u := hs u v
  linarith

lemma variational_derivativeAt (V : E → E) (Phi : ℝ × E → E) (t : ℝ) (x : E)
    (hV : DifferentiableAt ℝ V (Phi (t,x))) (hPhi : ContDiffAt ℝ ∞ Phi (t,x))
    (hODE : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s => Phi (s,y)) (V (Phi (t,y))) t) :
    HasDerivAt (fun s => fderiv ℝ (fun y => Phi (s,y)) x)
      ((fderiv ℝ V (Phi (t,x))).comp (fderiv ℝ (fun y => Phi (t,y)) x)) t := by
  let D := fderiv ℝ Phi
  let A := fderiv ℝ D (t,x)
  let L : ((ℝ × E) →L[ℝ] E) →L[ℝ] E →L[ℝ] E :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip (ContinuousLinearMap.inr ℝ ℝ E)
  let T : ((ℝ × E) →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E (1,0)
  have hD : ContDiffAt ℝ 1 D (t,x) := hPhi.fderiv_right (by
    change (2 : ℕ∞ω) ≤ ∞
    exact WithTop.coe_le_coe.mpr le_top)
  have hedge : ∀ᶠ q in 𝓝 (t,x), DifferentiableAt ℝ Phi q := by
    filter_upwards [(hPhi.of_le (show (1 : ℕ∞ω) ≤ ∞ by norm_num)).eventually (by simp)] with q hq
    exact hq.differentiableAt one_ne_zero
  have ht : (fun s => fderiv ℝ (fun y => Phi (s,y)) x) =ᶠ[𝓝 t] fun s => L (D (s,x)) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hedge] with s hs
    exact (hs.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)).fderiv
  have hB : (fun y => V (Phi (t,y))) =ᶠ[𝓝 x] fun y => T (D (t,y)) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hedge, hODE] with y hy hode
    have h := (hy.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t y)).hasDerivAt
    exact (h.unique hode).symm
  have hd1 := (T.hasFDerivAt.comp (t,x) (hD.differentiableAt one_ne_zero).hasFDerivAt).comp x
    (hasFDerivAt_prodMk_right t x)
  have hder : (T.comp A).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      (fderiv ℝ V (Phi (t,x))).comp (fderiv ℝ (fun y => Phi (t,y)) x) := by
    have hd2 := hV.hasFDerivAt.comp x
      ((hPhi.differentiableAt (by norm_num)).comp x ((differentiableAt_const t).prodMk differentiableAt_id)).hasFDerivAt
    exact (hd1.congr_of_eventuallyEq hB).unique hd2
  have hJ := L.hasFDerivAt.comp_hasDerivAt t
    (((hD.differentiableAt one_ne_zero).hasFDerivAt.comp t
      (hasFDerivAt_prodMk_left t x)).hasDerivAt)
  have hsym := hPhi.isSymmSndFDerivAt (show minSmoothness ℝ 2 ≤ ∞ by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  have heq : L (A (1,0)) = (fderiv ℝ V (Phi (t,x))).comp
      (fderiv ℝ (fun y => Phi (t,y)) x) := by
    rw [← hder]
    ext v
    exact hsym (1,0) (0,v)
  change HasDerivAt (fun s => L (D (s,x))) (L (A (1,0))) t at hJ
  rw [heq] at hJ
  exact hJ.congr_of_eventuallyEq ht

lemma pullback_derivative_zeroAt
    (w : E → TwoForm (E := E)) (V : E → E) (H : E → ℝ)
    (Phi : ℝ × E → E) (t : ℝ) (x u v : E)
    (hw : DifferentiableAt ℝ w (Phi (t,x)))
    (hV : DifferentiableAt ℝ V (Phi (t,x))) (hH : ContDiffAt ℝ ∞ H (Phi (t,x)))
    (halt : ∀ᶠ y in 𝓝 (Phi (t,x)), ∀ a, w y a a = 0)
    (hclosed : ∀ a b c, fderiv ℝ w (Phi (t,x)) a b c +
      fderiv ℝ w (Phi (t,x)) b c a + fderiv ℝ w (Phi (t,x)) c a b = 0)
    (hham : ∀ᶠ y in 𝓝 (Phi (t,x)), ∀ a, w y (V y) a = fderiv ℝ H y a)
    (hPhi : ContDiffAt ℝ ∞ Phi (t,x))
    (hODE : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s => Phi (s,y)) (V (Phi (t,y))) t) :
    HasDerivAt (fun s => w (Phi (s,x)) (fderiv ℝ (fun y => Phi (s,y)) x u)
      (fderiv ℝ (fun y => Phi (s,y)) x v)) 0 t := by
  have hwc := HasFDerivAt.comp_hasDerivAt (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E) t hw.hasFDerivAt hODE.self_of_nhds
  have hJ := variational_derivativeAt V Phi t x hV hPhi hODE
  have hu := (ContinuousLinearMap.apply ℝ E u).hasFDerivAt.comp_hasDerivAt t hJ
  have hv := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivAt t hJ
  have h := (hwc.clm_apply hu).clm_apply hv
  have he := infinitesimal_preservationAt w V H (Phi (t,x)) hw hV hH halt hclosed hham
    (fderiv ℝ (fun y => Phi (t,y)) x u) (fderiv ℝ (fun y => Phi (t,y)) x v)
  change HasDerivAt (fun s => w (Phi (s,x)) (fderiv ℝ (fun y => Phi (s,y)) x u)
    (fderiv ℝ (fun y => Phi (s,y)) x v)) _ t at h
  convert! h using 1
  simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.comp_apply, add_apply] using he.symm

theorem hamiltonian_flow_preserves_form
    (w : E → TwoForm (E := E)) (V : E → E) (H : E → ℝ)
    (hw : ContDiff ℝ ∞ w) (hV : ContDiff ℝ ∞ V) (hH : ContDiff ℝ ∞ H)
    (halt : ∀ x u, w x u u = 0)
    (hclosed : ∀ x u v z, fderiv ℝ w x u v z +
      fderiv ℝ w x v z u + fderiv ℝ w x z u v = 0)
    (hham : ∀ x u, w x (V x) u = fderiv ℝ H x u)
    (Phi : ℝ × E → E) (hPhi : ContDiff ℝ ∞ Phi)
    (hzero : ∀ x, Phi (0,x) = x)
    (hODE : ∀ t x, HasDerivAt (fun s => Phi (s,x)) (V (Phi (t,x))) t)
    (t : ℝ) (x u v : E) :
    w (Phi (t,x)) (fderiv ℝ (fun y => Phi (t,y)) x u)
      (fderiv ℝ (fun y => Phi (t,y)) x v) = w x u v := by
  let f : ℝ → ℝ := fun s => w (Phi (s,x))
    (fderiv ℝ (fun y => Phi (s,y)) x u)
    (fderiv ℝ (fun y => Phi (s,y)) x v)
  have hd (s : ℝ) : HasDerivAt f 0 s :=
    pullback_derivative_zeroAt w V H Phi s x u v
      (hw.differentiable (by simp) _) (hV.differentiable (by simp) _)
      hH.contDiffAt (Filter.Eventually.of_forall (fun y => halt y))
      (hclosed _) (Filter.Eventually.of_forall (fun y => hham y))
      hPhi.contDiffAt (Filter.Eventually.of_forall (fun y => hODE s y))
  have he : f t = f 0 := is_const_of_deriv_eq_zero
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  have hz : (fun y => Phi (0,y)) = id := funext hzero
  simpa only [f, hz, fderiv_id, fderiv_fun_id, ContinuousLinearMap.id_apply, hzero] using he

end
end MorseArnold.SymplecticFlow

end

end OAI
