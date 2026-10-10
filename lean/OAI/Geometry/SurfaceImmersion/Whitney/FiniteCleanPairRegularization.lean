import OAI.Geometry.SurfaceImmersion.Atlas.FiniteChartTranslationBound
import OAI.Geometry.SurfaceImmersion.Geometry.FrozenTranslationGerms
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSurfaceImmersionStability
import OAI.Geometry.SurfaceImmersion.Whitney.CompactSurfacePairStability
import OAI.Geometry.SurfaceImmersion.Geometry.FinitePairPatchCover
import OAI.Geometry.SurfaceImmersion.Whitney.FixedPairPointAvoidance
import OAI.Geometry.SurfaceImmersion.Whitney.CleanSurfacePairs

namespace OAI

/-! Finite regularization with both transversality and finite-point avoidance,
including preservation on an initially good compact set and C1 control. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι κ ν : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem finite_surface_pair_clean_relative
    (p q : ι → M) (P : ∀ i, SurfacePairTranslationPatch (p i) (q i))
    (T : ι → Set (M × M)) (hT : ∀ i, IsCompact (T i))
    (hTP : ∀ i, T i ⊆ (P i).U ×ˢ (P i).V)
    (A : κ → Set M)
    (hPA : ∀ i j, ((P i).χ =ᶠ[𝓝ˢ (A j)] (fun _ => 0)) ∨
      ((P i).χ =ᶠ[𝓝ˢ (A j)] (fun _ => 1)))
    (S : Set M) (hS : S.Finite) (J : Set (M × M)) (hJ : IsCompact J)
    [Fintype ν] (c : ν → M) (Q : ν → Set JetPolynomial.Base)
    (hQ : ∀ j, IsCompact (Q j)) (hQT : ∀ j, Q j ⊆ (chart (c j)).target)
    (s : Finset ι) (B : Set M) (hB : IsCompact B) {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hIf : ∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x))
    (hJreg : J ⊆ cleanSurfacePairs f S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      FrozenTranslationGerms A f g ∧ (∀ x, ‖g x-f x‖ < ε) ∧
      ChartDerivativeClose c Q f g ε ∧
      (∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)) ∧
      (J ⊆ cleanSurfacePairs g S) ∧
      ∀ i ∈ s, T i ⊆ cleanSurfacePairs g S := by
  classical
  induction s using Finset.induction_on generalizing ε with
  | empty =>
    exact ⟨f,hf,frozenTranslationGerms_refl A f,by simpa using fun _ : M => hε,by intro j x hx; simpa using hε,hIf,hJreg,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨g,hg,hfg,hclose,hDc,hIg,hJg,hgood⟩ := ih (half_pos hε)
    let K := J ∪ ⋃ j ∈ s, T j
    have hK : IsCompact K := hJ.union (s.isCompact_biUnion (fun j _ => hT j))
    have hKreg : K ⊆ cleanSurfacePairs g S := by
      intro z hz
      rcases hz with hz | hz
      · exact hJg hz
      · obtain ⟨j,hj,hzj⟩ := mem_iUnion₂.mp hz
        exact hgood j hj hzj
    obtain ⟨δ,hδ,hstable⟩ := compact_clean_pair_stability hg (P i).smooth (P i).bounds hK hS hKreg
    obtain ⟨η,hη,hηI⟩ := compact_surface_immersion_stability hg (P i).smooth hB hIg
    obtain ⟨ζ,hζ,hζD⟩ := finite_chart_translation_bound c Q hQ hQT (P i).smooth (half_pos hε)
    obtain ⟨a,ha,hnew⟩ := (P i).regularize_avoiding_points hg S S hS hS (lt_min hδ (lt_min hη (lt_min hζ (half_pos hε))))
    let G := surfaceTranslation g (P i).χ a
    have haδ : ‖a‖ < δ := ha.trans_le (min_le_left _ _)
    have haη : ‖a‖ < η := ha.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have haζ : ‖a‖ < ζ := ha.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have haε : ‖a‖ < ε/2 := ha.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    refine ⟨G,surfaceTranslation_smooth hg (P i).smooth a,
      hfg.trans (frozenTranslationGerms_translate (hPA i) g a),?_,?_,hηI a haη,?_,?_⟩
    · intro x
      have hx : ‖G x-g x‖ < ε/2 := by
        change ‖g x+(P i).χ x • a-g x‖ < ε/2
        rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ((P i).bounds x).1]
        exact (mul_le_mul_of_nonneg_right ((P i).bounds x).2 (norm_nonneg a)).trans_lt (by simpa using haε)
      calc
        ‖G x-f x‖ ≤ ‖G x-g x‖+‖g x-f x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε/2+ε/2 := add_lt_add hx (hclose x)
        _ = ε := by ring
    · intro j x hx
      have hd := hζD hg a haζ j x hx
      calc
        _ ≤ ‖fderiv ℝ (G ∘ (chart (c j)).symm) x-fderiv ℝ (g ∘ (chart (c j)).symm) x‖+
            ‖fderiv ℝ (g ∘ (chart (c j)).symm) x-fderiv ℝ (f ∘ (chart (c j)).symm) x‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε/2+ε/2 := add_lt_add hd (hDc j x hx)
        _ = ε := by ring
    · intro z hz
      exact hstable a haδ (Or.inl hz)
    · intro j hj z hz
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact mem_cleanSurfacePairs.mpr (hnew z.1 (hTP j hz).1 z.2 (hTP j hz).2)
      · exact hstable a haδ (Or.inr (mem_iUnion₂.mpr ⟨j,hj,hz⟩))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
