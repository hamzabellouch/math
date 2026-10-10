import OAI.Geometry.Relativity.CKS.InducedMetric

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma localMax_second_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (h : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hmin := isLocalMin_of_deriv_deriv_pos hp h.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [h,hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hd : deriv f =ᶠ[𝓝 x] (fun _ => 0) := by simpa using he.deriv
  have hz : deriv (deriv f) x = 0 := by simpa using hd.deriv_eq
  linarith

lemma affineLine_hasDerivAt (y a : E2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => y+s•a) a t := by
  simpa using ((hasDerivAt_id t).smul_const a).const_add y

lemma line_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E2 → V} {y : E2} (hf : DifferentiableAt ℝ f y) (a : E2) :
    deriv (fun t : ℝ => f (y+t•a)) 0 = fderiv ℝ f y a := by
  have hh : HasFDerivAt f (fderiv ℝ f y) (y+(0:ℝ)•a) := by simpa using hf.hasFDerivAt
  exact (hh.comp_hasDerivAt 0 (affineLine_hasDerivAt y a 0)).deriv

lemma line_second_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E2 → V} {y : E2} (hf : ContDiffAt ℝ ∞ f y) (a : E2) :
    deriv (deriv (fun t : ℝ => f (y+t•a))) 0 =
      fderiv ℝ (fun z => fderiv ℝ f z a) y a := by
  have he : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ f z :=
    ((hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by simp)).mono
      (fun _ h => h.differentiableAt (by simp))
  have hline : Tendsto (fun t : ℝ => y+t•a) (𝓝 0) (𝓝 y) := by
    have hh := (affineLine_hasDerivAt y a 0).continuousAt
    change Tendsto _ _ (𝓝 (y+(0:ℝ)•a)) at hh
    simpa using hh
  have hh : deriv (fun t : ℝ => f (y+t•a)) =ᶠ[𝓝 0]
      (fun t => fderiv ℝ f (y+t•a) a) := by
    filter_upwards [hline he] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (affineLine_hasDerivAt y a t)).deriv
  rw [hh.deriv_eq]
  exact line_deriv (((hf.fderiv_right (by simp : ∞+1 ≤ ∞)).clm_apply contDiffAt_const).differentiableAt (by simp)) a

lemma curve_normSq_second {c : ℝ → E3} {t : ℝ} (hc : ContDiffAt ℝ ∞ c t) :
    deriv (deriv (fun s => ‖c s‖^2)) t =
      2 * (⟪deriv c t,deriv c t⟫_ℝ + ⟪c t,deriv (deriv c) t⟫_ℝ) := by
  have he : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ c s :=
    ((hc.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by simp)).mono
      (fun _ h => h.differentiableAt (by simp))
  have hder : deriv (fun s => ‖c s‖^2) =ᶠ[𝓝 t]
      (fun s => 2*⟪c s,deriv c s⟫_ℝ) := by
    filter_upwards [he] with s hs
    have hd := hs.hasDerivAt.inner ℝ hs.hasDerivAt
    simpa [real_inner_self_eq_norm_sq,real_inner_comm (deriv c s) (c s),two_mul] using hd.deriv
  rw [hder.deriv_eq]
  have hd := (hc.differentiableAt (by simp)).hasDerivAt.inner ℝ
    (((hc.derivWithin (by simp : ∞+1 ≤ ∞)).differentiableAt (by simp)).hasDerivAt)
  convert (hd.const_mul 2).deriv using 1
  ring

lemma maximum_radius_hessian {f : E2 → E3} {y : E2}
    (hf : ContDiffAt ℝ ∞ f y) (hm : IsLocalMax (fun z => ‖f z‖^2) y) (a : E2) :
    ⟪f y, fderiv ℝ (fun z => fderiv ℝ f z a) y a⟫_ℝ ≤
      -⟪fderiv ℝ f y a, fderiv ℝ f y a⟫_ℝ := by
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => f (y+t•a)) 0 := by
    have hh : ContDiffAt ℝ ∞ f (y+(0:ℝ)•a) := by simpa using hf
    exact hh.comp 0 (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hmax : IsLocalMax (fun t : ℝ => ‖f (y+t•a)‖^2) 0 := by
    have hh : IsLocalMax (fun z => ‖f z‖^2) (y+(0:ℝ)•a) := by simpa using hm
    exact hh.comp_continuous (g := fun t : ℝ => y+t•a) (b := 0) (affineLine_hasDerivAt y a 0).continuousAt
  have hh := localMax_second_deriv_nonpos hmax (hc.continuousAt.norm.pow 2)
  rw [curve_normSq_second hc, line_second_deriv hf a,
    line_deriv (hf.differentiableAt (by simp)) a] at hh
  simpa using (show ⟪f (y+(0:ℝ)•a), fderiv ℝ (fun z => fderiv ℝ f z a) y a⟫_ℝ ≤
    -⟪fderiv ℝ f y a,fderiv ℝ f y a⟫_ℝ from by linarith)

end CKSSchwarzschild

end

end OAI
