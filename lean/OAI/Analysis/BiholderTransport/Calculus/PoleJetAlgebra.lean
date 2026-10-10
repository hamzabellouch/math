import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.JetPullback
import OAI.Analysis.BiholderTransport.Calculus.TaylorPositivity

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma HasSecondTaylor.const_mul {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) (c:ℝ) :
    HasSecondTaylor (fun h => c*f h) (c • l) (c • B) := by
  unfold HasSecondTaylor at *
  have he : (fun h => c*f h-c*f 0-(c • l) h-(c • B) h h/2) =
      (fun h => c*(f h-f 0-l h-B h h/2)) := by
    funext h; simp only [smul_apply,smul_eq_mul]; ring
  rw [he]
  exact hf.const_mul_left c

lemma pole_nonneg_of_envelope_taylor {f : E → ℝ} {p : E} {t : ℝ}
    {R : E →L[ℝ] E}
    (hf : HasSecondTaylor (fun h => f (p+h)) (t • innerSL ℝ p)
      (t • innerSL ℝ-(innerSL ℝ).comp R))
    (hupper : ∀ᶠ q in 𝓝 p, f q≤f p+t*(‖q‖^2/2-‖p‖^2/2))
    (d:E) : 0 ≤ inner ℝ (R d) d := by
  have H := ((norm_square_hasSecondTaylor p).const_mul t).sub hf
  have He : t • innerSL ℝ p-t • innerSL ℝ p = (0 : E →L[ℝ] ℝ) := sub_self _
  have HB : t • innerSL ℝ-(t • innerSL ℝ-(innerSL ℝ).comp R)=(innerSL ℝ).comp R :=
    sub_sub_cancel _ _
  rw [He,HB] at H
  have hm : IsLocalMin (fun h => t*(‖p+h‖^2/2)-f (p+h)) 0 := by
    have ht : Tendsto (fun h:E => p+h) (𝓝 0) (𝓝 p) := by
      simpa only [ContinuousAt,add_zero] using
        (show ContinuousAt (fun h:E => p+h) 0 from by fun_prop)
    filter_upwards [ht.eventually hupper] with h hh
    simp only [add_zero]
    linarith
  exact H.nonneg_of_localMin hm d

lemma pole_kernel_of_active_support {B : E×E → ℝ} {D f : E → ℝ}
    {a : E → E} {p pj : E} {t : ℝ} {R : E →L[ℝ] E}
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (hf : HasFDerivAt f (t • innerSL ℝ p) p)
    (hB : DifferentiableAt ℝ B (0,p))
    (hBa : ∀ u v:E, fderiv ℝ B (0,p) (u,v) = -inner ℝ p u+t*inner ℝ p v)
    (hD : HasFDerivAt D (-innerSL ℝ pj) 0)
    (hm : IsLocalMin (fun q => f q-B (a q,q)+D (a q)) p)
    (hsym : ∀ u v:E, inner ℝ (R u) v=inner ℝ u (R v)) : R (pj-p)=0 := by
  have hB' : HasFDerivAt B (fderiv ℝ B (0,p)) (a p,p) := by
    rw [ha0]; exact hB.hasFDerivAt
  have hD' : HasFDerivAt D (-innerSL ℝ pj) (a p) := by rwa [ha0]
  have hder := (hf.sub (hB'.comp (f := fun q => (a q,q)) p
    (ha.prodMk (hasFDerivAt_id (𝕜 := ℝ) p)))).add (hD'.comp p ha)
  have H := hm.hasFDerivAt_eq_zero hder
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have he := congrArg (fun l : E →L[ℝ] ℝ => l (R (pj-p))) H
  simp only [add_apply,sub_apply,smul_apply,neg_apply,zero_apply,
    smul_eq_mul,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply] at he
  rw [hBa] at he
  have horth : inner ℝ (pj-p) (R (R (pj-p)))=0 := by
    rw [inner_sub_left]
    linarith
  rw [←hsym] at horth
  exact horth

end WeakMTWTransport

end

end OAI
