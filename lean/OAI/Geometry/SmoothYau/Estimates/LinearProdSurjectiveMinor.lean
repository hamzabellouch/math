import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
lemma linear_prod_surjective_of_minor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L R : E →L[ℝ] ℝ) (v w : E) (h : L v*R w-L w*R v ≠ 0) :
    Function.Surjective (L.prod R) := by
  rintro ⟨a,b⟩
  let D := L v*R w-L w*R v
  refine ⟨((a*R w-b*L w)/D) • v+((b*L v-a*R v)/D) • w, ?_⟩
  apply Prod.ext
  · change L (_ • v+_ • w)=a
    simp only [map_add,map_smul,smul_eq_mul]
    calc
      _ = a*D/D := by dsimp only [D]; ring
      _ = a := mul_div_cancel_right₀ a h
  · change R (_ • v+_ • w)=b
    simp only [map_add,map_smul,smul_eq_mul]
    calc
      _ = b*D/D := by dsimp only [D]; ring
      _ = b := mul_div_cancel_right₀ b h
lemma analytic_rank_dense {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (hf : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g)
    {x₀ : E} (hr : Function.Surjective (fderiv ℝ (fun x => (f x,g x)) x₀))
    {O : Set E} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ y ∈ O, Function.Surjective (fderiv ℝ (fun x => (f x,g x)) y) := by
  have hd (x : E) : fderiv ℝ (fun x => (f x,g x)) x = (fderiv ℝ f x).prod (fderiv ℝ g x) :=
    (hf.differentiable (by simp) x).fderiv_prodMk (hg.differentiable (by simp) x)
  obtain ⟨v,hv⟩ := hr (1,0)
  obtain ⟨w,hw⟩ := hr (0,1)
  rw [hd] at hv hw
  have hv1 := congrArg Prod.fst hv
  have hv2 := congrArg Prod.snd hv
  have hw1 := congrArg Prod.fst hw
  have hw2 := congrArg Prod.snd hw
  simp only [ContinuousLinearMap.prod_apply] at hv1 hv2 hw1 hw2
  let D : E → ℝ := fun x => fderiv ℝ f x v*fderiv ℝ g x w-fderiv ℝ f x w*fderiv ℝ g x v
  have hD : ContDiff ℝ ω D := by
    have H (q : E → ℝ) (hq : ContDiff ℝ ω q) (z : E) :
        ContDiff ℝ ω (fun x => fderiv ℝ q x z) :=
      (hq.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
    exact ((H f hf v).mul (H g hg w)).sub ((H f hf w).mul (H g hg v))
  by_contra! hn
  obtain ⟨z,hz⟩ := hne
  have he : D =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
    filter_upwards [hO.mem_nhds hz] with x hx
    by_contra hh
    apply hn x hx
    rw [hd]
    exact linear_prod_surjective_of_minor _ _ v w hh
  have hglo := hD.analyticOnNhd.eq_of_eventuallyEq contDiff_const.analyticOnNhd he
  have := congrFun hglo x₀
  simp only [D,hv1,hv2,hw1,hw2] at this
  norm_num at this
end YauCounterexamples
end

end OAI
