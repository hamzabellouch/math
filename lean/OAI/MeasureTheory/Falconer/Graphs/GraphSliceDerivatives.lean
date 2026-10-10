import OAI.MeasureTheory.Falconer.Graphs.GraphAmplitudeSupport

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

theorem graph_z_slice_derivative_le {f : (Plane × ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (η : Plane) (z : ℝ) (n : ℕ) :
    ‖iteratedDeriv n (fun t => f (η,t)) z‖ ≤ ‖iteratedFDeriv ℝ n f (η,z)‖ := by
  let g : (Plane × ℝ) → ℂ := fun p => f (p+(η,0))
  let L : ℝ →L[ℝ] (Plane × ℝ) := ContinuousLinearMap.inr ℝ Plane ℝ
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have he : (fun t => f (η,t)) = g ∘ L := by funext t; simp [g,L]
  rw [he,← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    L.iteratedFDeriv_comp_right hg z (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hn : ‖L‖ = 1 := ContinuousLinearMap.norm_inr ℝ Plane ℝ
  simp only [hn,Finset.prod_const_one,mul_one]
  dsimp only [g]
  rw [iteratedFDeriv_comp_add_right]
  simp [L]

theorem graph_z_slice_tsupport {f : (Plane × ℝ) → ℂ}
    (hs : tsupport f ⊆ graphAmplitudeCompact) (η : Plane) :
    tsupport (fun t => f (η,t)) ⊆ Icc (-4:ℝ) 4 := by
  apply closure_minimal _ isClosed_Icc
  intro z hz
  exact (hs (subset_closure hz)).1.2

theorem GraphDerivativeBound.z_slice {n : ℕ} {f : (Plane × ℝ) → ℂ} {C D : ℝ}
    (hf : GraphDerivativeBound n f C D) (hs : tsupport f ⊆ graphAmplitudeCompact)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (η : Plane) :
    ContDiff ℝ ∞ (fun z => f (η,z)) ∧
      tsupport (fun z => f (η,z)) ⊆ Icc (-4:ℝ) 4 ∧
      ∀ j ≤ n, ∀ z, ‖iteratedDeriv j (fun t => f (η,t)) z‖ ≤ C*D^j := by
  have hg := hf.global_smooth hs
  refine ⟨hg.comp (contDiff_const.prodMk contDiff_id),graph_z_slice_tsupport hs η,?_⟩
  intro j hj z
  exact (graph_z_slice_derivative_le hg η z j).trans (hf.global_bound hs hC hD j hj (η,z))

end PlanarFalconer

end OAI
