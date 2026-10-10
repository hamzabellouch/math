import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeAntiNorms

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricChart
open ComplexMatrix TemperedDistribution HilbertSobolev Bundle Set Filter
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma hodge_lift_unit_estimate
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
      (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
    (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
      weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
        ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ C₀*M)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) (u : MetricUnit g) :
    ∃ C : ℝ, ∃ V : Set (MetricUnit g), 0 ≤ C ∧ IsOpen V ∧ u ∈ V ∧
      ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 → ∀ a : PreL2 A J α hs ht true,
        ∀ v ∈ V,
          ‖eval (closedLiftOfInverse A J α hs ht H Gs (smoothAntiProjection A J α hs ht a)).val
            v.val.proj v.val.2 (J.endomorphism v.val.proj v.val.2)‖ ≤
            C*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖ := by
  obtain ⟨p,hp,hq⟩ := exists_nonzero_weight_chart A J α ht (fun p => (D p).toData) hD u.val.proj
  have hsrc : u.val.proj ∈ (extChartAt Model p.val).source :=
    (D p).source_subset (hD p (subset_closure hp))
  have hw : coordinateWeight A p ((extChartAt Model p.val) u.val.proj) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hsrc] using hp
  obtain ⟨O,hO,hqO,_,C,hC,hbound⟩ :=
    hodge_lift_local_estimate A J α hs ht D hD H Gs hH hweak C₀ hC₀ hdual p _ hq hw
  let U : Set X := (extChartAt Model p.val).source ∩ (extChartAt Model p.val) ⁻¹' O
  have hU : IsOpen U := (continuousOn_extChartAt p.val).isOpen_inter_preimage
    (isOpen_extChartAt_source p.val) hO
  have hb : Continuous (fun v : MetricUnit g => v.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hpre : (fun v : MetricUnit g => v.val.proj) ⁻¹' U ∈ 𝓝 u :=
    (hU.preimage hb).mem_nhds ⟨hsrc,hqO⟩
  have hfac : ContinuousAt (fun v : MetricUnit g => chartDirectionFactor J p.val v.val) u :=
    (chartDirectionFactor_continuousAt J p.val u.val hsrc).comp continuous_subtype_val.continuousAt
  have hfacN : ∀ᶠ v : MetricUnit g in 𝓝 u,
      chartDirectionFactor J p.val v.val < chartDirectionFactor J p.val u.val + 1 :=
    hfac (gt_mem_nhds (by linarith))
  obtain ⟨V,hVs,hV,huV⟩ := mem_nhds_iff.mp (inter_mem hpre hfacN)
  have hLc : 0 ≤ chartDirectionFactor J p.val u.val + 1 :=
    add_nonneg (chartDirectionFactor_nonneg J p.val u.val) zero_le_one
  refine ⟨C*(chartDirectionFactor J p.val u.val+1),V,mul_nonneg hC hLc,hV,huV,?_⟩
  intro r hr hr1 a v hv
  rw [closedLiftOfInverse_complexLine]
  have h₁ := eval_le_chartDirectionFactor J p.val
    (exteriorDerivative (codifferential J α ht (Gs (smoothAntiProjection A J α hs ht a)).val.val))
      v.val (hVs hv).1.1
  have h₂ := hbound r hr hr1 a ((extChartAt Model p.val) v.val.proj) (hVs hv).1.2
  calc
    _ ≤ _ := h₁
    _ ≤ (C*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖)*
        (chartDirectionFactor J p.val u.val+1) :=
      mul_le_mul h₂ (hVs hv).2.le (chartDirectionFactor_nonneg J p.val v.val)
        (by positivity)
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricChart
open ComplexMatrix TemperedDistribution HilbertSobolev Bundle Set Filter
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma hodge_lift_global_estimate
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
      (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
    (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
      weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
        ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ C₀*M)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ a : PreL2 A J α hs ht true,
        ‖smoothUnitEvaluation J g
          (closedLiftOfInverse A J α hs ht H Gs (smoothAntiProjection A J α hs ht a))‖ ≤
          C*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖ := by
  classical
  choose C U hC hU hu hb using
    hodge_lift_unit_estimate A J α hs ht D hD H Gs hH hweak C₀ hC₀ hdual g
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun u _ => mem_iUnion.mpr ⟨u,hu u⟩)
  let L : ℝ := ∑ i : s, C i.val
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i _ => hC i.val)
  refine ⟨L,hL,fun r hr hr1 a => ?_⟩
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ L*(r⁻¹)^3*
    ‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖)).mpr
  intro u
  obtain ⟨i,hi,hui⟩ := mem_iUnion₂.mp (hscover (mem_univ u))
  have hCi : C i ≤ L := Finset.single_le_sum (fun j _ => hC j.val) (Finset.mem_univ (⟨i,hi⟩ : s))
  exact (hb i r hr hr1 a u hui).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCi (by positivity)) (norm_nonneg _))

include D hD in

lemma exists_closed_lift_hodge_bound
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    ∃ B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2,
      (∀ f, IsClosed (B f).val) ∧
      (∀ f, antiInvariantPart J (B f).val = f.val.val) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
        ∀ a : PreL2 A J α hs ht true,
          ‖smoothUnitEvaluation J g (B (smoothAntiProjection A J α hs ht a))‖ ≤
            C*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖ := by
  obtain ⟨H,Gs,hH,_,hweak,hclosed,hright,C₀,hC₀,hdual⟩ :=
    exists_closed_lift_dual_data A J α hs ht (fun p => (D p).toData) hD
  obtain ⟨C,hC,hb⟩ := hodge_lift_global_estimate A J α hs ht D hD H Gs hH hweak C₀ hC₀ hdual g
  exact ⟨closedLiftOfInverse A J α hs ht H Gs,hclosed,hright,C,hC,hb⟩
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
