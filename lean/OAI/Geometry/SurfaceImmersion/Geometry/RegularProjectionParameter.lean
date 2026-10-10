import OAI.Geometry.SurfaceImmersion.Geometry.GenericProjectionParameter
import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateSardThree

namespace OAI

/-! Regular graph-projection parameters in dimension three. Unlike the
higher-dimensional avoidance result, this gives finite exceptional
directions on compact coordinate sets. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem exists_regular_projection_parameter {ι : Type*} [Countable ι]
    (H : ι → Base → Base →L[ℝ] ProjectionTarget 3 × ℝ)
    (hH : ∀ i, ContDiff ℝ ∞ (H i))
    (U : Set (ProjectionTarget 3)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ a ∈ U, ∀ i b z, z ∈ tangentSlopeDomain (H i) b →
      tangentSlope (H i) b z = a →
      Function.Surjective (fderiv ℝ (tangentSlope (H i) b) z) := by
  let bad : Set (ProjectionTarget 3) := ⋃ i, ⋃ b : Bool,
    tangentSlope (H i) b '' {z | z ∈ tangentSlopeDomain (H i) b ∧
      ¬ Function.Surjective (fderiv ℝ (tangentSlope (H i) b) z)}
  have hbad : volume bad = 0 := measure_iUnion_null (fun i =>
    measure_iUnion_null (fun b => PublishedInputs.smooth_coordinate_critical_values_null
      _ _ (tangentSlopeDomain_open (hH i) b) (tangentSlope_smoothOn (hH i) b)))
  have hae : ∀ᵐ a ∂volume, a ∉ bad := by
    simp only [ae_iff,not_not]
    change volume bad = 0
    exact hbad
  obtain ⟨a,haU,ha⟩ := (Measure.dense_of_ae hae).inter_open_nonempty U hU hne
  refine ⟨a,haU,?_⟩
  intro i b z hz he
  by_contra hn
  apply ha
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨b,⟨z,⟨hz,hn⟩,he⟩⟩⟩

def compactProjectionDirections (a : ProjectionTarget 3)
    (H : Base → Base →L[ℝ] ProjectionTarget 3 × ℝ) (K : Set Base) (b : Bool) :
    Set (Base × ℝ) :=
  (K ×ˢ Icc (-1 : ℝ) 1) ∩ {z | graphProjection a (H z.1 (tangentRay b z.2)) = 0}

theorem finite_compact_projection_directions
    {H : Base → Base →L[ℝ] ProjectionTarget 3 × ℝ}
    (hH : ContDiff ℝ ∞ H) {K : Set Base} (hK : IsCompact K)
    (hI : ∀ x ∈ K, Function.Injective (H x)) (a : ProjectionTarget 3) (b : Bool)
    (hreg : ∀ z, z ∈ tangentSlopeDomain H b → tangentSlope H b z = a →
      Function.Surjective (fderiv ℝ (tangentSlope H b) z)) :
    (compactProjectionDirections a H K b).Finite := by
  let C := compactProjectionDirections a H K b
  have hcomp : IsCompact C := (hK.prod isCompact_Icc).inter_right
    (isClosed_eq ((graphProjection a).continuous.comp
      ((hH.comp contDiff_fst).clm_apply
        ((tangentRay_smooth b).comp contDiff_snd)).continuous) continuous_const)
  have hU : C ⊆ tangentSlopeDomain H b := by
    intro z hz
    have he : (H z.1 (tangentRay b z.2)).1 =
        (H z.1 (tangentRay b z.2)).2 • a := sub_eq_zero.mp hz.2
    intro hs
    have he0 : H z.1 (tangentRay b z.2) = H z.1 0 := by
      rw [map_zero]
      apply Prod.ext
      · change (H z.1 (tangentRay b z.2)).1 = 0
        simpa only [hs,zero_smul] using he
      · exact hs
    exact tangentRay_ne_zero b z.2 (hI z.1 hz.1.1 he0)
  have heq (z) (hz : z ∈ C) : tangentSlope H b z = a := by
    have he : (H z.1 (tangentRay b z.2)).1 =
        (H z.1 (tangentRay b z.2)).2 • a := sub_eq_zero.mp hz.2
    change (H z.1 (tangentRay b z.2)).2⁻¹ • (H z.1 (tangentRay b z.2)).1 = a
    rw [he,smul_smul,inv_mul_cancel₀ (hU hz),one_smul]
  have hfin := PublishedInputs.finite_compact_coordinate_regular_fiber
    (tangentSlopeDomain_open hH b) (tangentSlope_smoothOn hH b) hcomp hU a
    (fun z _ he => hreg z (hU ‹z ∈ C›) he)
  exact hfin.subset (fun z hz => ⟨hz,heq z hz⟩)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
