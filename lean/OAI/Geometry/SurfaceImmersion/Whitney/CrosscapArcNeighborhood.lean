import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapCompactArc

namespace OAI

/-! The compact half-arc contains a whole neighborhood of its endpoint
in the compactified double curve. -/
noncomputable section
open Set Filter Metric Manifold Topology
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M] in
lemma unorderedPair_mem_square {U : Set M} {z : M × M} :
    unorderedPair z ∈ unorderedPair '' (U ×ˢ U) ↔ z ∈ U ×ˢ U := by
  change z ∈ unorderedPair ⁻¹' (unorderedPair '' (U ×ˢ U)) ↔ _
  rw [unorderedPair_preimage_image]
  simp only [mem_union,mem_prod,mem_preimage,Prod.fst_swap,Prod.snd_swap]
  tauto

theorem crosscap_arc_contains_neighborhood {F : M → ProjectionTarget 3}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
    {δ : ℝ} (hδ : 0 < δ) (γ : Icc (0 : ℝ) δ → UnorderedSurfacePairs M)
    (hγ : ∀ s, γ s = unorderedPair
      ((chart q).symm (chart q p+(s:ℝ) • tangentRay b t),
        (chart q).symm (chart q p-(s:ℝ) • tangentRay b t))) :
    ∃ V : Set (UnorderedSurfacePairs M), IsOpen V ∧ unorderedPair (p,p) ∈ V ∧
      compactifiedDoubleCurve F ∩ V ⊆ Set.range γ := by
  obtain ⟨r,hr,_hball,_hformula,hiso,hdouble⟩ :=
    surface_quadratic_crosscap_chart F p q hp hφ he b t hz hreg
  let a := chart q p
  let w := tangentRay b t
  have hw : w ≠ 0 := tangentRay_ne_zero b t
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let ρ := min r (δ*‖w‖)
  have hρ : 0 < ρ := lt_min hr (mul_pos hδ hwn)
  let U := (chart q).source ∩ (chart q) ⁻¹' ball a ρ
  have hU : IsOpen U := (chart q).isOpen_inter_preimage isOpen_ball
  have hpU : p ∈ U := ⟨hp,mem_ball_self hρ⟩
  let V := unorderedPair '' (U ×ˢ U)
  refine ⟨V,unorderedPair_isOpenMap _ (hU.prod hU),⟨(p,p),⟨hpU,hpU⟩,rfl⟩,?_⟩
  rintro z ⟨⟨⟨u,v⟩,hcl,hzq⟩,hzV⟩
  rw [← hzq] at hzV ⊢
  have hUV : (u,v) ∈ U ×ˢ U := unorderedPair_mem_square.mp hzV
  have huS : u ∈ (chart q).source := hUV.1.1
  have hvS : v ∈ (chart q).source := hUV.2.1
  let x := chart q u
  let y := chart q v
  have hxρ : x ∈ ball a ρ := hUV.1.2
  have hyρ : y ∈ ball a ρ := hUV.2.2
  have hxr : x ∈ ball a r := ball_subset_ball (min_le_left _ _) hxρ
  have hyr : y ∈ ball a r := ball_subset_ball (min_le_left _ _) hyρ
  by_cases huv : u = v
  · have hdiag : (u,u) ∈ closure (surfaceDoublePairs F) := by simpa only [huv] using hcl
    have hbad := doublePairs_closure_diagonal_singular hF u hdiag
    have hxsing : ¬ Function.Injective
        (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F ((chart q).symm x)) := by
      rw [show (chart q).symm x = u from (chart q).left_inv huS]
      exact hbad
    have hxa : x = a := (hiso x hxr).mp hxsing
    have hup : u = p := (chart q).injOn huS hp hxa
    refine ⟨⟨0,le_rfl,hδ.le⟩,?_⟩
    rw [hγ]
    simp [hup,← huv,(chart q).left_inv hp]
  · have hxy : x ≠ y := fun h => huv ((chart q).injOn huS hvS h)
    have heqF : F u = F v := doublePairs_closure_equal hF.continuous hcl
    have hfxy : F ((chart q).symm x) = F ((chart q).symm y) := by
      rw [show (chart q).symm x = u from (chart q).left_inv huS,
        show (chart q).symm y = v from (chart q).left_inv hvS]
      exact heqF
    obtain ⟨s,_hs,hxs,hys⟩ := (hdouble x hxr y hyr hxy).mp hfxy
    have hnorm : |s| * ‖w‖ < ρ := by
      have h := mem_ball.mp hxρ
      change ‖x-a‖ < ρ at h
      rw [hxs,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] at h
      exact h
    have hsδ : |s| < δ := by
      exact (mul_lt_mul_iff_left₀ hwn).mp (hnorm.trans_le (min_le_right _ _))
    let s' : Icc (0 : ℝ) δ := ⟨|s|,abs_nonneg s,hsδ.le⟩
    refine ⟨s',?_⟩
    have hu : u = (chart q).symm (a+s • w) := by rw [← hxs]; exact ((chart q).left_inv huS).symm
    have hv : v = (chart q).symm (a-s • w) := by rw [← hys]; exact ((chart q).left_inv hvS).symm
    have habs : unorderedLinePair a w s = unorderedLinePair a w |s| := by
      apply (unorderedLinePair_eq_iff a w hw s |s|).mpr
      rcases le_total 0 s with hs | hs
      · exact Or.inl (abs_of_nonneg hs).symm
      · exact Or.inr (by rw [abs_of_nonpos hs,neg_neg])
    have hmap := congrArg (unorderedPairMap (chart q).symm) habs
    rw [hγ,hu,hv]
    exact hmap.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
