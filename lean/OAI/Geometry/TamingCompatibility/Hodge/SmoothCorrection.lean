import Mathlib
import OAI.Geometry.TamingCompatibility.Currents.UnitMeasureBound
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothGeometricInverse

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def smoothAntiProjection : smoothForms X 2 →ₗ[ℝ] antiPre A J α hs ht where
  toFun β := ⟨⟨antiInvariantPart J β.val, IsSmooth.antiInvariantPart β.property J⟩,
    antiInvariantPart_idempotent J β.val⟩
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact antiInvariantPart_add J a.val b.val
  map_smul' c a := by
    apply Subtype.ext
    apply Subtype.ext
    exact antiInvariantPart_smul J c a.val

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma invariant_of_anti_zero (β : TwoForm X) (hβ : antiInvariantPart J β = 0) :
    IsInvariant β J := by
  have he := invariantPart_add_antiInvariantPart J β
  rw [hβ,add_zero] at he
  rw [← he]
  exact invariantPart_isInvariant J β

variable (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hs hD in

theorem correct_smooth_functional
    (P : smoothForms X 2 →ₗ[ℝ] ℝ)
    (hP : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J → P β = 0) :
    ∃ Q : smoothForms X 2 →ₗ[ℝ] ℝ,
      (∀ β : smoothForms X 2, IsClosed β.val → (P+Q) β = 0) ∧
      (∀ β : smoothForms X 2,
        Q ⟨antiInvariantPart J β.val,IsSmooth.antiInvariantPart β.property J⟩ = Q β) := by
  obtain ⟨B,hBc,hBR⟩ := exists_smooth_closed_lift A J α hs ht D hD
  let R := smoothAntiProjection A J α hs ht
  let C := B.comp R
  let Q : smoothForms X 2 →ₗ[ℝ] ℝ := -(P.comp C)
  refine ⟨Q,?_,?_⟩
  · intro β hβ
    have hc : IsClosed (β-C β).val := by
      apply (mem_closedForms_iff (β-C β)).mp
      apply Submodule.sub_mem
      · exact (mem_closedForms_iff β).mpr hβ
      · exact (mem_closedForms_iff (C β)).mpr (hBc (R β))
    have hi : IsInvariant (β-C β).val J := by
      apply invariant_of_anti_zero J
      have he : R (C β) = R β := by
        apply Subtype.ext
        apply Subtype.ext
        exact hBR (R β)
      have hz : R (β-C β) = 0 := by rw [map_sub,he,sub_self]
      exact congrArg (fun a : antiPre A J α hs ht => a.val.val) hz
    have hz := hP (β-C β) hc hi
    change P β - P (C β) = 0
    simpa only [map_sub] using hz
  · intro β
    have he : R ⟨antiInvariantPart J β.val,IsSmooth.antiInvariantPart β.property J⟩ = R β := by
      apply Subtype.ext
      apply Subtype.ext
      exact antiInvariantPart_idempotent J β.val
    change -(P (B (R _))) = -(P (B (R β)))
    rw [he]

include hs hD in

theorem exists_nonzero_smooth_correction [Nonempty X]
    (hc : IsClosed α)
    (hn : ¬ ∃ η : TwoForm X, IsSymplectic η ∧ Compatible η J) :
    ∃ P Q : smoothForms X 2 →ₗ[ℝ] ℝ,
      (∀ β : smoothForms X 2, Tames β.val J → 0 < P β) ∧
      (∀ β : smoothForms X 2, IsClosed β.val → (P+Q) β = 0) ∧
      (∀ β : smoothForms X 2,
        Q ⟨antiInvariantPart J β.val,IsSmooth.antiInvariantPart β.property J⟩ = Q β) ∧ Q ≠ 0 := by
  obtain ⟨μ,hμ,-,-,hP,hpos⟩ := exists_geometric_separating_current J α hs ht hn
  let := hμ
  let P := unitMeasureCurrent J (hermitianMetric J α hs ht) μ
  obtain ⟨Q,hPQ,hQ⟩ := correct_smooth_functional A J α hs ht D hD P hP
  refine ⟨P,Q,hpos,hPQ,hQ,?_⟩
  intro hzero
  have hz := hPQ ⟨α,hs⟩ hc
  rw [hzero,add_zero] at hz
  exact (ne_of_gt (hpos ⟨α,hs⟩ ht)) hz

end TamingCompatibility.GeometricHilbert

end

end OAI
