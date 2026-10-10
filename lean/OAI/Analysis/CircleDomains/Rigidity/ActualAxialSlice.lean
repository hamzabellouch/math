import OAI.Analysis.CircleDomains.Rigidity.MatchedSliceEstimate
import OAI.Analysis.CircleDomains.Rigidity.CompactScalarAxialDerivative
import OAI.Analysis.CircleDomains.Sobolev.SphereScalarLineSmooth
import OAI.Analysis.CircleDomains.Rigidity.TypicalAxialDiskTolls

namespace OAI

/-! The slice estimate for the actual selected finite field and actual
complex derivative, with no assumed variation or image-length bound. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] Classical.propDecidable
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem actual_axial_slice_estimate [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hsΦ : HasCompactSupport Φ)
    {W : Set ℂ} (hW : IsOpen W) (k : Fin 2)
    (hcoord : ∀ p ∈ (f '' G)ᶜ, sphereFromPlaneFunction Φ p =
      (complexPlaneCoordinates.symm (finiteCoord p)) k)
    (hrel : ∀ z ∈ W, ∀ p, D.planeRelation z p → sphereFromPlaneFunction Φ p =
      (complexPlaneCoordinates.symm (finiteCoord p)) k)
    (i : Fin 2) (y : ℝ)
    (htrace : volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) k) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (htoll : Summable (fun j : D.IndexedMatchedPair =>
      (Icc (transverseCoordinate i (E.sourceCenter j)-E.sourceRadius j)
        (transverseCoordinate i (E.sourceCenter j)+E.sourceRadius j)).indicator
          (fun _ => 2*E.targetRadius j) y))
    {a b : ℝ} (hab : a ≤ b) (F : Finset D.IndexedMatchedPair)
    (hsegment : ∀ x ∈ Icc a b, complexCoordinateLine i y x ∈ W)
    (havoid : ∀ x ∈ Icc a b, ∀ j ∈ F, (complexCoordinateLine i y x : Sphere) ∉ j.val.1)
    (hρ : IntegrableOn (fun x => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere)))
        (complexCoordinateLine i y x)‖)
      (Icc a b ∩ {x | (complexCoordinateLine i y x : Sphere) ∈ G}) volume) :
    |(complexPlaneCoordinates.symm (D.selectedPlane hG.1 hf (complexCoordinateLine i y b))) k-
      (complexPlaneCoordinates.symm (D.selectedPlane hG.1 hf (complexCoordinateLine i y a))) k| ≤
      (∫ x in Icc a b ∩ {x | (complexCoordinateLine i y x : Sphere) ∈ G},
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) (complexCoordinateLine i y x)‖) +
      ∑' j : {j : D.IndexedMatchedPair // j ∉ F},
        if ∃ x ∈ Icc a b, (complexCoordinateLine i y x : Sphere) ∈ j.val.val.1
          then 2*E.targetRadius j else 0 := by
  let φ := sphereFromPlaneFunction Φ
  let bφ := fun z : ℂ => φ (f (z : Sphere))
  let U := {x | (complexCoordinateLine i y x : Sphere) ∈ G}
  let V := Icc a b ∩ U
  have hline := (complexCoordinateLine_contDiff i y).continuous
  have hU : IsOpen U := hG.1.preimage (OnePoint.continuous_coe.comp hline)
  have hV : MeasurableSet V := measurableSet_Icc.inter hU.measurableSet
  have hsm := D.sphere_scalar_line_contDiffOn hG.1 hinf hf hfix hΦ i y
  have hmajor (x : ℝ) (hx : x ∈ V) :
      |deriv (fun t => bφ (complexCoordinateLine i y t)) x| ≤
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) (complexCoordinateLine i y x)‖ := by
    apply compact_scalar_axial_deriv_le
      (hW.inter (hG.1.preimage OnePoint.continuous_coe)) i k y x
      ⟨hsegment x hx.1,hx.2⟩
      ((analyticAt_finite_map_of_conformal hG.1 hf.1 hx.2
        (D.planeRelation_ne_infty hG.1 hinf hf hfix (D.componentRelation_graph hf hx.2))).differentiableAt)
    intro z hz
    exact hrel z hz.1 _ (D.componentRelation_graph hf hz.2)
  have hdermeas : AEStronglyMeasurable (fun x =>
      |deriv (fun t => bφ (complexCoordinateLine i y t)) x|) (volume.restrict V) :=
    ((hsm.continuousOn_deriv_of_isOpen hU le_rfl).abs.mono inter_subset_right).aestronglyMeasurable hV
  have hi : IntegrableOn (fun x => |deriv (fun t => bφ (complexCoordinateLine i y t)) x|) V volume :=
    hρ.mono' hdermeas (by
      filter_upwards [ae_restrict_mem hV] with x hx
      simpa only [Real.norm_eq_abs,abs_abs] using hmajor x hx)
  have hnull : volume ((fun x => φ (D.selectedTarget hG.1 hf (complexCoordinateLine i y x : Sphere))) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0 := by
    convert htrace using 1
    congr 1
    apply image_congr
    intro x hx
    exact hcoord _ (D.selectedTarget_outside hG.1 hf hx.1)
  have hsum : Summable (fun j : {j : D.IndexedMatchedPair // j ∉ F} =>
      if ∃ x ∈ Icc a b, (complexCoordinateLine i y x : Sphere) ∈ j.val.val.1
        then 2*E.targetRadius j else 0) := by
    have h := (segment_disk_tolls_summable i E.sourceCenter E.sourceRadius E.targetRadius
      E.target_nonneg htoll a b).subtype (fun j => j ∉ F)
    convert h using 1
    funext j
    congr 1
    congr 1
    funext x
    rw [E.source_eq]
    simp only [OnePoint.coe_injective.eq_iff,mem_image,exists_eq_right]
  have hslice := D.scalar_slice_estimate E hG hinf hf hH hinf' hline
    (smooth_compact_sphere_scalar hΦ hsΦ).1 k hcoord hab F havoid hnull hsm hi hsum
  have ha := hrel _ (hsegment a (left_mem_Icc.mpr hab)) _ (D.selectedTarget_mem hG.1 hf _)
  have hb := hrel _ (hsegment b (right_mem_Icc.mpr hab)) _ (D.selectedTarget_mem hG.1 hf _)
  rw [ha,hb] at hslice
  exact hslice.trans (add_le_add (setIntegral_mono_on hi hρ hV hmajor) le_rfl)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
