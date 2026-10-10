import OAI.Geometry.SurfaceImmersion.Geometry.FrozenTranslationGerms
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSurfaceImmersionStability
import OAI.Geometry.SurfaceImmersion.Whitney.CompactSurfacePairStability
import OAI.Geometry.SurfaceImmersion.Geometry.FinitePairPatchCover
import OAI.Geometry.SurfaceImmersion.Whitney.FixedPairPointAvoidance
import OAI.Geometry.SurfaceImmersion.Geometry.CompactPairAvoidance

namespace OAI

/-! Finite pair regularization also eliminates coincidences at a prescribed finite
set, while preserving earlier pieces, regularity, and frozen crosscap germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem finite_surface_pair_regularization_avoiding_points
    (p q : ι → M) (P : ∀ i, SurfacePairTranslationPatch (p i) (q i))
    (T : ι → Set (M × M)) (hT : ∀ i, IsCompact (T i))
    (hTP : ∀ i, T i ⊆ (P i).U ×ˢ (P i).V)
    (A : κ → Set M)
    (hPA : ∀ i j, ((P i).χ =ᶠ[𝓝ˢ (A j)] (fun _ => 0)) ∨
      ((P i).χ =ᶠ[𝓝ˢ (A j)] (fun _ => 1)))
    (S : Set M) (hS : S.Finite) (s : Finset ι) (B : Set M) (hB : IsCompact B) {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hIf : ∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      FrozenTranslationGerms A f g ∧ (∀ x, ‖g x-f x‖ < ε) ∧
      (∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)) ∧
      ∀ i ∈ s, ∀ z ∈ T i, g z.1 = g z.2 →
        z.1 ∉ S ∧ z.2 ∉ S ∧ Function.Surjective (surfacePairDerivative g z.1 z.2) := by
  classical
  induction s using Finset.induction_on generalizing ε with
  | empty =>
    exact ⟨f,hf,frozenTranslationGerms_refl A f,by simpa using fun _ : M => hε,hIf,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨g,hg,hfg,hclose,hIg,hgood⟩ := ih (half_pos hε)
    let K := ⋃ j ∈ s, T j
    have hK : IsCompact K := s.isCompact_biUnion (fun j _ => hT j)
    have hKavoid : ∀ z ∈ K, z.1 ∈ S ∨ z.2 ∈ S → g z.1 ≠ g z.2 := by
      intro z hz hzS heq
      obtain ⟨j,hj,hzj⟩ := mem_iUnion₂.mp hz
      have hh := hgood j hj z hzj heq
      rcases hzS with hz1 | hz2
      · exact hh.1 hz1
      · exact hh.2.1 hz2
    have hKreg : ∀ z ∈ K, g z.1 = g z.2 → Function.Surjective (surfacePairDerivative g z.1 z.2) := by
      intro z hz
      obtain ⟨j,hj,hzj⟩ := mem_iUnion₂.mp hz
      exact fun heq => (hgood j hj z hzj heq).2.2
    obtain ⟨δ,hδ,hstable⟩ := compact_surface_pair_stability hg (P i).smooth hK hKreg
    obtain ⟨ζ,hζ,havoid⟩ := compact_finite_pair_avoidance_stability hg.continuous
      (P i).χ (P i).bounds hK hS hKavoid
    obtain ⟨η,hη,hηI⟩ := compact_surface_immersion_stability hg (P i).smooth hB hIg
    obtain ⟨a,ha,hnew⟩ := (P i).regularize_avoiding_points hg S S hS hS
      (lt_min hδ (lt_min hζ (lt_min hη (half_pos hε))))
    let G := surfaceTranslation g (P i).χ a
    have haδ : ‖a‖ < δ := ha.trans_le (min_le_left _ _)
    have haζ : ‖a‖ < ζ := ha.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have haη : ‖a‖ < η := ha.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have haε : ‖a‖ < ε/2 := ha.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    refine ⟨G,surfaceTranslation_smooth hg (P i).smooth a,
      hfg.trans (frozenTranslationGerms_translate (hPA i) g a),?_,hηI a haη,?_⟩
    · intro x
      have hx : ‖G x-g x‖ < ε/2 := by
        change ‖g x+(P i).χ x • a-g x‖ < ε/2
        rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ((P i).bounds x).1]
        exact (mul_le_mul_of_nonneg_right ((P i).bounds x).2 (norm_nonneg a)).trans_lt (by simpa using haε)
      calc
        ‖G x-f x‖ ≤ ‖G x-g x‖+‖g x-f x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε/2+ε/2 := add_lt_add hx (hclose x)
        _ = ε := by ring
    · intro j hj z hz hzz
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hnew z.1 (hTP j hz).1 z.2 (hTP j hz).2 hzz
      · have hzK : z ∈ K := mem_iUnion₂.mpr ⟨j,hj,hz⟩
        have hn : ¬ (z.1 ∈ S ∨ z.2 ∈ S) := fun h => havoid a haζ z hzK h hzz
        exact ⟨(not_or.mp hn).1,(not_or.mp hn).2,hstable a haδ z hzK hzz⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
