import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace Y]

lemma lower_support_of_nonnegative_hessian {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) (hf : ∀ z∈S, ContDiffAt ℝ 2 f z)
    (hH : ∀ z∈S, ∀ d : E, 0 ≤ fderiv ℝ (fderiv ℝ f) z d d)
    {x y : E} (hx : x∈S) (hy : y∈S) :
    f x+fderiv ℝ f x (y-x) ≤ f y := by
  let d := y-x
  let l : ℝ → E := fun t => x+t • d
  let g : ℝ → ℝ := fun t => f (l t)
  let g' : ℝ → ℝ := fun t => fderiv ℝ f (l t) d
  let g'' : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ f) (l t) d d
  have hl : ∀ t∈Icc (0:ℝ) 1, l t∈S := by
    intro t ht
    have H := hS hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
    convert H using 1
    dsimp [l,d]
    module
  have hld (t : ℝ) : HasDerivAt l d t := by
    simpa only [l,id_eq,one_smul] using (((hasDerivAt_id t).smul_const d).const_add x)
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g (g' t) t :=
    ((hf (l t) (hl t ht)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hld t)
  have hg' (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g' (g'' t) t := by
    have H := (((hf (l t) (hl t ht)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hld t)
    simpa only [g',g'',Function.comp_apply,map_zero,add_zero] using H.clm_apply (hasDerivAt_const t d)
  have hconv : ConvexOn ℝ (Icc (0:ℝ) 1) g :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (hg' t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hH _ (hl t (interior_subset ht)) d)
  have H := hconv.deriv_le_slope (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one) zero_lt_one (hg 0 (by constructor <;> norm_num)).differentiableAt
  rw [(hg 0 (by constructor <;> norm_num)).deriv] at H
  simp only [g,g',l,d,zero_smul,add_zero,one_smul,add_sub_cancel,slope,
    sub_zero,inv_one,one_smul,vsub_eq_sub] at H
  linarith

lemma bilinear_nonnegative_of_norm_sub_le {B H : E →L[ℝ] E →L[ℝ] ℝ} {m : ℝ}
    (hB : ∀ d, m*‖d‖^2 ≤ B d d) (hH : ‖H-B‖≤ m) (d : E) : 0≤H d d := by
  have hn := (H-B).le_opNorm₂ d d
  have hmul := mul_le_mul_of_nonneg_right hH (sq_nonneg ‖d‖)
  have hdiff : H d d-B d d ≤ ‖(H-B) d d‖ := le_abs_self _
  have hdiff' : -(H d d-B d d) ≤ ‖(H-B) d d‖ := neg_le_abs _
  have he : ‖H-B‖*‖d‖*‖d‖=‖H-B‖*‖d‖^2 := by ring
  rw [he] at hn
  have H' := hB d
  nlinarith

lemma exists_local_mountains {F : Y → E → ℝ} {x : E} {y : Y} {m : ℝ}
    (hm : 0< m)
    (hC : ContinuousAt (fun q : E×Y => fderiv ℝ (fderiv ℝ (F q.2)) q.1) (x,y))
    (hD : ∀ᶠ q : E×Y in 𝓝 (x,y), ContDiffAt ℝ 2 (F q.2) q.1)
    (hpos : ∀ d:E, m*‖d‖^2 ≤ fderiv ℝ (fderiv ℝ (F y)) x d d) :
    ∃ r>0, ∃ V∈𝓝 y, ∀ y'∈V, ∀ z∈Metric.closedBall x r,
      fderiv ℝ (F y') z=0 → ∀ w∈Metric.closedBall x r, F y' z≤F y' w := by
  have H := @ContinuousAt.norm (E×Y) (E →L[ℝ] E →L[ℝ] ℝ) _ _ _ _
    (hC.sub (continuousAt_const (y := fderiv ℝ (fderiv ℝ (F y)) x)))
  have Hn : ∀ᶠ q : E×Y in 𝓝 (x,y),
      ‖fderiv ℝ (fderiv ℝ (F q.2)) q.1-fderiv ℝ (fderiv ℝ (F y)) x‖< m := by
    apply H.eventually_lt continuousAt_const
    simpa only [Pi.sub_apply,Prod.fst,Prod.snd,sub_self,ContinuousLinearMap.opNorm_zero] using hm
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp (Hn.and hD)
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  refine ⟨r,hr,V,hV,?_⟩
  intro y' hy' z hz hs w hw
  have Hlow := lower_support_of_nonnegative_hessian (f := F y') (convex_closedBall x r)
    (fun u hu => (hUV (a := (u,y')) ⟨hrU hu,hy'⟩).2)
    (fun u hu d => bilinear_nonnegative_of_norm_sub_le hpos
      (hUV (a := (u,y')) ⟨hrU hu,hy'⟩).1.le d) hz hw
  simpa only [hs,zero_apply,add_zero] using Hlow

end WeakMTWTransport

end

end OAI
