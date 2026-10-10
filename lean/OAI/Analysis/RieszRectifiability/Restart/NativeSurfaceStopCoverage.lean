import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.NativeSurfaceArea
import OAI.Analysis.RieszRectifiability.Restart.ProjectionStopShadowMass
import OAI.Analysis.RieszRectifiability.Projections.ProjectedAreaSelection

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem nativeSurfaceArea_eq_hausdorff_of_subset {n d : ℕ}
    (A B : Set (Ambient d)) (hB : MeasurableSet B) (hsub : B ⊆ A) :
    nativeSurfaceArea n A B = (μH[(n : ℝ)] : Measure (Ambient d)) B := by
  rw [nativeSurfaceArea_apply A B hB, inter_eq_right.mpr hsub]

theorem native_surface_lattice_exceptional_hausdorff_null {n d : ℕ}
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (R : ℝ) (hR : 0 < R) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (supportLatticeExceptional ν R hR) = 0 := by
  have hsub : supportLatticeExceptional ν R hR ⊆ A := by
    intro x hx
    obtain ⟨t, ht⟩ := mem_iUnion.mp hx
    exact hsupport ▸ supportLatticeOverlap_subset_support ν R hR t ht
  have heq := nativeSurfaceArea_eq_hausdorff_of_subset (n := n) A (supportLatticeExceptional ν R hR)
    (supportLatticeExceptional_measurable ν R hR) hsub
  rw [← heq, ← hν]
  exact supportLatticeExceptional_null ν C G hC hG hg hlower R hR

theorem native_surface_core_disk_le_survivor_add_shadow {n d : ℕ}
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points)
    (Good : SupportCellDescendant ν R hR k z → Prop)
    (T : Ambient d → Ambient n) (hT : LipschitzWith 1 T)
    (hcover : closedBall (T z) (latticeRadius R k / 32) ⊆
      T '' (ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16))) :
    (μH[(n : ℝ)] : Measure (Ambient n)) (closedBall (T z) (latticeRadius R k / 32)) ≤
      ν (cellRegionLimit ν R hR k z Good) +
        (μH[(n : ℝ)] : Measure (Ambient n))
          (T '' (⋃ i : cellRegionStops ν R hR k z Good, i.val.cell)) := by
  let E := cellRegionLimit ν R hR k z Good
  let B := supportLatticeExceptional ν R hR
  let W := ⋃ i : cellRegionStops ν R hR k z Good, i.val.cell
  have hB : (μH[(n : ℝ)] : Measure (Ambient d)) B = 0 :=
    native_surface_lattice_exceptional_hausdorff_null ν A hν hsupport C G hC hG hg hlower R hR
  have hTB : (μH[(n : ℝ)] : Measure (Ambient n)) (T '' B) = 0 := by
    have h := hT.hausdorffMeasure_image_le (show 0 ≤ (n : ℝ) by positivity) B
    simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul, hB] at h
    exact le_antisymm h (zero_le)
  have hshadow : T '' ((ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16)) \ E) ⊆
      T '' W ∪ T '' B := by
    rintro _ ⟨x, ⟨hx, hxE⟩, rfl⟩
    by_cases hxB : x ∈ B
    · exact Or.inr ⟨x, hxB, rfl⟩
    have hxcell : x ∈ cleanSupportCell ν R hR k z := by
      refine ⟨(supportLatticeCell_bounds ν R hR k z).1 ⟨hx.1, ?_⟩, hxB⟩
      exact closedBall_subset_ball (by have hr := latticeRadius_pos R hR k; linarith) hx.2
    obtain ⟨i, hi, hxi⟩ := exists_first_failing_cell ν R hR k z Good x hxcell hxE
    exact Or.inl ⟨x, mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩, rfl⟩
  have hproj := projected_cover_le_retained_area_add_shadow n T hT
    (ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16)) E
    (closedBall (T z) (latticeRadius R k / 32)) (T '' W ∪ T '' B) hcover hshadow
  have hEsub : E ⊆ A := by
    intro x hx
    exact hsupport ▸ supportLatticeCell_subset_support ν R hR k z hx.1.1
  have hEeq : (μH[(n : ℝ)] : Measure (Ambient d)) E = ν E := by
    rw [hν]
    exact (nativeSurfaceArea_eq_hausdorff_of_subset A E
      (cellRegionLimit_measurable ν R hR k z Good) hEsub).symm
  have hfirst : (μH[(n : ℝ)] : Measure (Ambient d))
      ((ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16)) ∩ E) ≤ ν E := by
    rw [← hEeq]
    exact measure_mono inter_subset_right
  have hsecond : (μH[(n : ℝ)] : Measure (Ambient n)) (T '' W ∪ T '' B) ≤
      (μH[(n : ℝ)] : Measure (Ambient n)) (T '' W) := by
    simpa only [hTB, add_zero] using! (measure_union_le (T '' W) (T '' B)
      (μ := (μH[(n : ℝ)] : Measure (Ambient n))))
  exact hproj.trans (add_le_add hfirst hsecond)

end

end RieszRectifiability

end OAI
