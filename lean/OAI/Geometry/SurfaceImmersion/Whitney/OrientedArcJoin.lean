import OAI.Geometry.SurfaceImmersion.Whitney.SmoothArcJoin

namespace OAI

/-! A concrete smooth joining operation for two regular oriented surface
arcs whose overlap is given by a smooth increasing coordinate change. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem join_oriented_regular_arcs {γ δ : ℝ → M} {h : ℝ → ℝ}
    {l b c d a : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hh : ContDiffOn ℝ ∞ h U) (haU : a ∈ U) (hpos : 0 < deriv h a)
    (hab : a < b) (hca : c < h a) (had : h a < d)
    (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ (Ioo l b))
    (hδ : ContMDiffOn 𝓘(ℝ) planeModel ∞ δ (Ioo c d))
    (hIγ : ∀ t ∈ Ioo l b, Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t))
    (hIδ : ∀ t ∈ Ioo c d, Function.Injective (mfderiv 𝓘(ℝ) planeModel δ t))
    (he : γ =ᶠ[𝓝 a] δ ∘ h) :
    ∃ (e : ℝ ≃ₜ ℝ) (G : ℝ → M),
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ StrictMono e ∧ e a = h a ∧
      a < e.symm d ∧ ContMDiffOn 𝓘(ℝ) planeModel ∞ G (Ioo l (e.symm d)) ∧
      (∀ t ∈ Ioo l (e.symm d), Function.Injective (mfderiv 𝓘(ℝ) planeModel G t)) ∧
      (∀ t, t ≤ a → G t = γ t) ∧ (∀ t, a < t → G t = δ (e t)) := by
  obtain ⟨e,hes,hei,hem,hee⟩ := local_increasing_diffeomorphism hU hh haU hpos
  have hea : e a = h a := hee.eq_of_nhds
  have hau : a < e.symm d := by
    apply hem.lt_iff_lt.mp
    rw [e.apply_symm_apply,hea]
    exact had
  have hge : γ =ᶠ[𝓝 a] δ ∘ e := by
    filter_upwards [he,hee] with t ht ht'
    exact ht.trans (congrArg δ ht'.symm)
  let G := joinedCurve a γ (δ ∘ e)
  have hdif : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ) 𝓘(ℝ) :=
    ⟨hes.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn,
      hei.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn⟩
  have hsource : ∀ t ∈ Ioo l (e.symm d), a ≤ t → e t ∈ Ioo c d := by
    intro t ht hat
    have hlow : h a ≤ e t := by rw [← hea]; exact hem.monotone hat
    refine ⟨hca.trans_le hlow,?_⟩
    have hu := hem ht.2
    rwa [e.apply_symm_apply] at hu
  have hGs : ContMDiffOn 𝓘(ℝ) planeModel ∞ G (Ioo l (e.symm d)) := by
    apply joinedCurve_smooth_on a
    · intro t ht hta
      exact hγ.contMDiffAt (isOpen_Ioo.mem_nhds ⟨ht.1,hta.trans_lt hab⟩)
    · intro t ht hat
      exact (hδ.contMDiffAt (isOpen_Ioo.mem_nhds (hsource t ht hat))).comp t hes.contMDiff.contMDiffAt
    · exact hge
  have hGI : ∀ t ∈ Ioo l (e.symm d), Function.Injective (mfderiv 𝓘(ℝ) planeModel G t) := by
    apply joinedCurve_regular_on a
    · intro t ht hta
      exact hIγ t ⟨ht.1,hta.trans_lt hab⟩
    · intro t ht hat
      rw [mfderiv_comp t
        ((hδ.contMDiffAt (isOpen_Ioo.mem_nhds (hsource t ht hat))).mdifferentiableAt (by simp))
        (hes.contMDiff.mdifferentiable (by simp) t)]
      exact (hIδ _ (hsource t ht hat)).comp (hdif.mfderiv_injective (mem_univ t))
    · exact hge
  refine ⟨e,G,hes,hei,hem,hea,hau,hGs,hGI,?_,?_⟩
  · intro t ht
    simp only [G,joinedCurve,ite_eq_left ht]
  · intro t ht
    simp only [G,joinedCurve,ite_eq_right (not_le.mpr ht),Function.comp_apply]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
