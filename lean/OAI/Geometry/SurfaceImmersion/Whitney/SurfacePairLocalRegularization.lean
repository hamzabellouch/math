import OAI.Geometry.SurfaceImmersion.Whitney.SurfacePairPatchTranslation

namespace OAI

/-! A fixed smooth scalar separator regularizes a neighborhood of one
ordered pair by arbitrarily small translations. It is locally constant
near a prescribed finite set, so those first jets are retained. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem surface_pair_local_regularization
    {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (S : Finset M) (p q : M) (hpq : p ≠ q) :
    ∃ (χ : M → ℝ) (U V : Set M),
      ContMDiff planeModel 𝓘(ℝ) ∞ χ ∧ (∀ x, χ x ∈ Icc 0 1) ∧
      (∀ x ∈ S, (χ =ᶠ[𝓝 x] (fun _ => 0)) ∨ (χ =ᶠ[𝓝 x] (fun _ => 1))) ∧
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ q ∈ V ∧
      ∀ ε > 0, ∃ a : ProjectionTarget 3, ‖a‖ < ε ∧
        ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ (surfaceTranslation f χ a) ∧
        (∀ x, ‖surfaceTranslation f χ a x-f x‖ < ε) ∧
        (∀ x ∈ S, mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (surfaceTranslation f χ a) x =
          mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) ∧
        ∀ x ∈ U, ∀ y ∈ V, surfaceTranslation f χ a x = surfaceTranslation f χ a y →
          Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) x y) := by
  obtain ⟨χ,hχ,hχbound,hχp,hχq,hχS⟩ := finite_germ_separator S p q hpq
  obtain ⟨Up,F,hUp,hpUp,hUps,hF,heF⟩ := surface_chart_representative hf p
  obtain ⟨Vq,G,hVq,hqVq,hVqs,hG,heG⟩ := surface_chart_representative hf q
  obtain ⟨Wp,hχWp,hWp,hpWp⟩ := _root_.mem_nhds_iff.mp hχp
  obtain ⟨Wq,hχWq,hWq,hqWq⟩ := _root_.mem_nhds_iff.mp hχq
  let U := Up ∩ Wp
  let V := Vq ∩ Wq
  have hU : IsOpen U := hUp.inter hWp
  have hV : IsOpen V := hVq.inter hWq
  refine ⟨χ,U,V,hχ,hχbound,hχS,hU,⟨hpUp,hpWp⟩,hV,⟨hqVq,hqWq⟩,?_⟩
  intro ε hε
  obtain ⟨a,ha,hreg⟩ := surface_pair_patch_translation p q hF hG hU hV
    (fun x hx => hUps hx.1) (fun x hx => hVqs hx.1)
    (heF.mono inter_subset_left) (heG.mono inter_subset_left)
    (fun x hx => hχWp hx.2) (fun x hx => hχWq hx.2) hε
  refine ⟨a,ha,surfaceTranslation_smooth hf hχ a,?_,?_,hreg⟩
  · intro x
    change ‖f x+χ x • a-f x‖ < ε
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg (hχbound x).1]
    exact (mul_le_mul_of_nonneg_right (hχbound x).2 (norm_nonneg a)).trans_lt (by simpa using ha)
  · intro x hx
    rcases hχS x hx with h0 | h1
    · exact surfaceTranslation_mfderiv hf h0 a
    · exact surfaceTranslation_mfderiv hf h1 a

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
