import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily

namespace OAI

/-! A compact smooth parameter family inherits uniform logarithmic
weight estimates from its joint derivatives. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CubicFirstMoment

lemma norm_iteratedFDeriv_slice_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : E × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : E) (u : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v => F (p,v)) u‖ ≤
      ‖iteratedFDeriv ℝ n F (p,u)‖ := by
  let G : E × ℝ → ℂ := fun z => F ((p,0)+z)
  have hG : ContDiff ℝ ∞ G := hF.comp (contDiff_const.add contDiff_id)
  have he : (fun v => F (p,v)) = G ∘ ContinuousLinearMap.inr ℝ E ℝ := by
    ext v
    simp [G]
  rw [he,(ContinuousLinearMap.inr ℝ E ℝ).iteratedFDeriv_comp_right hG u (by exact_mod_cast le_top)]
  have hb := (iteratedFDeriv ℝ n G ((ContinuousLinearMap.inr ℝ E ℝ) u)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ E ℝ)
  simp only [ContinuousLinearMap.norm_inr,Finset.prod_const_one,mul_one] at hb
  exact hb.trans_eq (by
    rw [iteratedFDeriv_comp_add_left n (p,0)]
    simp)

/-- Only compactness of the parameter range, joint smoothness and common
support are needed; no Mellin estimate is assumed. -/
def uniformLogWeights_compactParameter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : Set E) (hK : IsCompact K)
    (W : E → ℝ → ℂ) (w : ℝ → ℂ)
    (hw : HasCompactSupport w) (hpos : tsupport w ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ w)
    (hW : ContDiff ℝ ∞ (Function.uncurry W))
    (hsupp : ∀ p ∈ K, Function.support (W p) ⊆ Function.support w) :
    UniformLogWeights (fun p : K => W p) := by
  let hconst := uniformLogWeights_constant (ι := Unit) w hw hpos hsm
  let F : E × ℝ → ℂ := fun z => W z.1 (Real.exp (-z.2))
  have he : ContDiff ℝ ∞ (fun z : E × ℝ => (z.1,Real.exp (-z.2))) := by fun_prop
  have hF : ContDiff ℝ ∞ F := hW.comp he
  have hlog (p : K) : tsupport (fun v => W p (Real.exp (-v))) ⊆
      tsupport (fun v => w (Real.exp (-v))) := by
    exact closure_mono (fun v hv => hsupp p p.property hv)
  refine ⟨fun p => hw.mono (hsupp p p.property),
    fun p => (closure_mono (hsupp p p.property)).trans hpos,
    fun p => hW.comp (contDiff_const.prodMk contDiff_id),
    hconst.radius,hconst.radius_nonneg,?_,?_⟩
  · intro p u hu
    exact hconst.support_bound () u (hlog p hu)
  · intro n
    let T := K ×ˢ Icc (-hconst.radius) hconst.radius
    have hT : IsCompact T := hK.prod isCompact_Icc
    obtain ⟨C,hC⟩ := hT.exists_bound_of_continuousOn
      ((hF.continuous_iteratedFDeriv (show (n:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).continuousOn)
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro p u
    by_cases hu : |u| ≤ hconst.radius
    · exact (norm_iteratedFDeriv_slice_le F hF p u n).trans
        ((hC (p,u) ⟨p.property,abs_le.mp hu⟩).trans (le_max_left _ _))
    · have hz : iteratedFDeriv ℝ n (fun v => W p (Real.exp (-v))) u = 0 := by
        by_contra hn
        have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
          (f := fun v => W p (Real.exp (-v))) n hn
        exact hu (hconst.support_bound () u (hlog p hs))
      rw [hz,norm_zero]
      exact le_max_right _ _

end CubicFirstMoment

end

end OAI
