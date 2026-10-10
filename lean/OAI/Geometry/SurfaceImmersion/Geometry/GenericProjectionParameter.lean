import OAI.Geometry.SurfaceImmersion.Geometry.ProjectionDirections
import OAI.Geometry.SurfaceImmersion.Geometry.LowerDimensionalRange

namespace OAI

/-! A common graph direction avoids every tangent plane in a finite family
of smooth surface-coordinate derivatives when the projection target has
dimension at least four. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {n : ℕ}
abbrev ProjectionTarget (n : ℕ) := EuclideanSpace ℝ (Fin n)

def tangentSlope (H : Base → Base →L[ℝ] ProjectionTarget n × ℝ)
    (b : Bool) (z : Base × ℝ) : ProjectionTarget n :=
  ((H z.1 (tangentRay b z.2)).2)⁻¹ • (H z.1 (tangentRay b z.2)).1

def tangentSlopeDomain (H : Base → Base →L[ℝ] ProjectionTarget n × ℝ)
    (b : Bool) : Set (Base × ℝ) :=
  {z | (H z.1 (tangentRay b z.2)).2 ≠ 0}

lemma tangentSlopeDomain_open {H : Base → Base →L[ℝ] ProjectionTarget n × ℝ}
    (hH : ContDiff ℝ ∞ H) (b : Bool) : IsOpen (tangentSlopeDomain H b) := by
  exact isOpen_compl_singleton.preimage ((hH.comp contDiff_fst).clm_apply
    ((tangentRay_smooth b).comp contDiff_snd)).continuous.snd

lemma tangentSlope_smoothOn {H : Base → Base →L[ℝ] ProjectionTarget n × ℝ}
    (hH : ContDiff ℝ ∞ H) (b : Bool) :
    ContDiffOn ℝ ∞ (tangentSlope H b) (tangentSlopeDomain H b) := by
  have h := (hH.comp contDiff_fst).clm_apply
    ((tangentRay_smooth b).comp contDiff_snd)
  exact (h.snd.contDiffOn.inv (fun _ hx => hx)).smul h.fst.contDiffOn

theorem tangentSlope_image_null (hn : 4 ≤ n)
    {H : Base → Base →L[ℝ] ProjectionTarget n × ℝ}
    (hH : ContDiff ℝ ∞ H) (b : Bool) :
    volume (tangentSlope H b '' tangentSlopeDomain H b) = 0 :=
  PublishedInputs.smooth_coordinate_parameter_image_null hn _ _
    (tangentSlopeDomain_open hH b) (tangentSlope_smoothOn hH b)

/-- The excluded parameters form a null set; therefore the projection can
be chosen in any prescribed nonempty open set of graph parameters. -/
theorem exists_common_projection_parameter (hn : 4 ≤ n)
    {ι : Type*} [Countable ι]
    (H : ι → Base → Base →L[ℝ] ProjectionTarget n × ℝ)
    (hH : ∀ i, ContDiff ℝ ∞ (H i))
    (U : Set (ProjectionTarget n)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ a ∈ U, ∀ i x, Function.Injective (H i x) →
      Function.Injective ((graphProjection a).comp (H i x)) := by
  let bad : Set (ProjectionTarget n) :=
    ⋃ i, ⋃ b : Bool, tangentSlope (H i) b '' tangentSlopeDomain (H i) b
  have hbad : volume bad = 0 :=
    measure_iUnion_null (fun i => measure_iUnion_null (fun b =>
      tangentSlope_image_null hn (hH i) b))
  have hae : ∀ᵐ a ∂volume, a ∉ bad := by
    simp only [ae_iff, not_not]
    change volume bad = 0
    exact hbad
  obtain ⟨a,hUa,ha⟩ := (Measure.dense_of_ae hae).inter_open_nonempty U hU hne
  refine ⟨a,hUa,fun i x hi => graphProjection_comp_injective a (H i x) hi ?_⟩
  intro b t ht he
  apply ha
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨b,⟨(x,t),ht,he.symm⟩⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
