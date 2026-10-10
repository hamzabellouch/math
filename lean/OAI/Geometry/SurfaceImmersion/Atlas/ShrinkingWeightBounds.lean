import OAI.Geometry.SurfaceImmersion.Atlas.ShrinkingWeightMultiplier
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSectionBounds

namespace OAI

/-! Uniform finite-order coordinate bounds for the actual radius family. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry WeightedEstimates

private lemma compact_parameter_slice_bounds {F : ℝ × SmallModes.Base → ℝ}
    (hF : ContDiff ℝ ∞ F) {K : Set ℝ} {Q : Set SmallModes.Base}
    (hK : IsCompact K) (hQ : IsCompact Q)
    (hs : ∀ r ∈ K, tsupport (fun x => F (r,x)) ⊆ Q) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ K,
      WeightedBound univ 1 m C (fun x => F (r,x)) := by
  obtain ⟨C,hC,hbound⟩ := compact_coefficient_bound uniqueDiffOn_univ
    (hK.prod hQ) (subset_univ _) hF.contDiffOn m
  refine ⟨C,zero_le_one.trans hC,?_⟩
  intro r hr j hj x _
  simp only [one_pow,one_mul,iteratedFDerivWithin_univ]
  by_cases hx : x ∈ Q
  · let L : SmallModes.Base →L[ℝ] ℝ × SmallModes.Base := ContinuousLinearMap.inr ℝ ℝ SmallModes.Base
    let G : ℝ × SmallModes.Base → ℝ := fun y => F (y+(r,0))
    have hG : ContDiff ℝ ∞ G := hF.comp (contDiff_id.add contDiff_const)
    have he : (fun x => F (r,x)) = G ∘ L := by
      funext y
      simp only [G,L,Function.comp_apply,ContinuousLinearMap.inr_apply,
        Prod.mk_add_mk,zero_add,add_zero]
    rw [he,L.iteratedFDeriv_comp_right hG x (by simp)]
    have hn := (iteratedFDeriv ℝ j G (L x)).norm_compContinuousLinearMap_le
      (fun _ : Fin j => L)
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hn
    have hder : iteratedFDeriv ℝ j G (L x) = iteratedFDeriv ℝ j F (r,x) := by
      simpa only [G,L,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,zero_add,add_zero]
        using iteratedFDeriv_comp_add_right j (r,0) (L x) (f := F)
    rw [hder] at hn
    have hbase : ‖iteratedFDeriv ℝ j F (r,x)‖ ≤ C := by
      simpa only [iteratedFDerivWithin_univ] using hbound j hj (r,x) ⟨hr,hx⟩
    rw [hder]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j F (r,x)‖ * ‖L‖^j := hn
      _ ≤ C * 1 := mul_le_mul hbase
        (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ ℝ SmallModes.Base))
        (pow_nonneg (norm_nonneg _) _) (zero_le_one.trans hC)
      _ = C := mul_one C
  · have hzero : iteratedFDeriv ℝ j (fun x => F (r,x)) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun hh => hx (hs r hr (tsupport_iteratedFDeriv_subset j hh))
    simp only [hzero,norm_zero]
    exact zero_le_one.trans hC

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

/-- One globally smooth coordinate multiplier represents all smaller ratio
weights; its product with the circular bump has uniform finite-order bounds. -/
theorem shrinkingWeight_coordinate_bounds (p : M) (w : M → ℝ)
    (hw : ContMDiff planeModel 𝓘(ℝ) ∞ w) {r0 R : ℝ}
    (hreg0 : circularCoordinateRegion p r0 ⊆ (coordinateChart p).target)
    (hR : R^2 < r0^2) :
    ∃ a : SmallModes.Base → ℝ, ContDiff ℝ ∞ a ∧
      (∀ r : ℝ, r^2 ≤ R^2 → ∀ x ∈ (coordinateChart p).target,
        shrinkingCircularWeight p w r0 r ((coordinateChart p).symm x) =
          a x * circularFlatBump (coordinateChart p p) r x) ∧
      ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ r : ℝ, r^2 ≤ R^2 →
        ∀ m, WeightedBound univ 1 m (C m)
          (fun x => a x * circularFlatBump (coordinateChart p p) r x) := by
  obtain ⟨b,hb,hbs,hbeq⟩ := exists_shrinkingWeight_multiplier p w hw hreg0 hR
  have hreg := (circularCoordinateRegion_mono p hR.le).trans hreg0
  have hlocal : ContDiffOn ℝ ∞ (fun x => b ((coordinateChart p).symm x))
      (coordinateChart p).target := by
    exact (hb.comp_contMDiffOn (coordinateChart_symm_smoothOn p)).contDiffOn
  obtain ⟨U,hU,hKU,_,a,ha,heq⟩ := CollarVelocity.compact_smooth_extension
    (circularCoordinateRegion_compact p R) (coordinateChart p).open_target hreg hlocal
  let F : ℝ × SmallModes.Base → ℝ := fun z => a z.2 *
    circularFlatBump (coordinateChart p p) z.1 z.2
  have hF : ContDiff ℝ ∞ F := (ha.comp contDiff_snd).mul
    (circularFlatBump_joint_smooth.comp
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd))
  have hs (r : ℝ) (hr : r ∈ Icc (-|R|) |R|) :
      tsupport (fun x => F (r,x)) ⊆ circularCoordinateRegion p R := by
    have hr2 : r^2 ≤ R^2 := by
      have h := (sq_le_sq₀ (abs_nonneg r) (abs_nonneg R)).2 (abs_le.mpr hr)
      simpa only [sq_abs] using h
    apply closure_minimal _ (isClosed_le (circularRadiusSquared_smooth _).continuous continuous_const)
    intro x hx
    by_contra hxQ
    have hzero := (circularFlatBump_zero_iff (coordinateChart p p) r x).mpr
      (hr2.trans (le_of_not_ge hxQ))
    exact hx (by simp only [F,hzero,mul_zero])
  choose C hC hbound using fun m => compact_parameter_slice_bounds hF
    (isCompact_Icc : IsCompact (Icc (-|R|) |R|))
    (circularCoordinateRegion_compact p R) hs m
  refine ⟨a,ha,?_,C,hC,?_⟩
  · intro r hr x hx
    rw [congrFun (hbeq r hr) ((coordinateChart p).symm x)]
    have hsx := (coordinateChart p).map_target hx
    simp only [circularManifoldBump,indicator_of_mem hsx,
      (coordinateChart p).right_inv hx]
    by_cases hmem : x ∈ circularCoordinateRegion p R
    · rw [heq (hKU hmem)]
    · have hz := (circularFlatBump_zero_iff (coordinateChart p p) r x).mpr
        (hr.trans (le_of_not_ge hmem))
      simp only [hz,mul_zero]
  · intro r hr m
    have habs : |r| ≤ |R| := (sq_le_sq₀ (abs_nonneg r) (abs_nonneg R)).1
      (by simpa only [sq_abs] using hr)
    exact hbound m r (abs_le.mp habs)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
