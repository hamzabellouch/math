import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.HilbertAtlas

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma integral_atlas {f : ℕ × Euc n → ℝ} (hf : Integrable f q.atlasMeasure) :
    ∫ w, f w ∂q.atlasMeasure = ∑' i, ∫ z, q.density i z*f (i,z) ∂volume.restrict (q.chart i).domain := by
  rw [atlasMeasure,integral_sum_measure hf]
  apply tsum_congr
  intro i
  rw [(measurableEmbedding_prodMk_left i).integral_map]
  rw [coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i _),smul_eq_mul]

lemma ae_atlas_of_chart {p : ℕ × Euc n → Prop}
    (h : ∀ i, ∀ᵐ z ∂volume.restrict (q.chart i).domain, p (i,z)) : ∀ᵐ w ∂q.atlasMeasure, p w := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  exact (withDensity_absolutelyContinuous _ _).ae_le (h i)

lemma ae_gradient_eq {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ w ∂q.atlasMeasure, q.gradient hu w = q.normalizedCovector w.1 u w.2 :=
  (q.memLp_gradientFunction hu).coeFn_toLp

lemma ae_gradient_bound {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ w ∂q.atlasMeasure, ‖q.gradient hu w‖ ≤ K := by
  filter_upwards [q.ae_gradient_eq hu,q.ae_gradientFunction_bound hu] with w he hb
  rw [he]
  exact hb
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal MatrixOrder

namespace CAT0Fillings
lemma dot_mulVec_sqrt_cross {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (u v : Fin n → ℝ) :
    u ⬝ᵥ P.mulVec v = (CFC.sqrt P).mulVec u ⬝ᵥ (CFC.sqrt P).mulVec v := by
  have hsym : (CFC.sqrt P).transpose = CFC.sqrt P :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg P).posSemidef.isHermitian).eq
  conv_lhs => rw [← CFC.sq_sqrt P hP.nonneg,pow_two, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym]
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma ae_normalizedCovector_inner (i : ℕ) (u v : X → ℝ) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      inner ℝ (q.normalizedCovector i u z) (q.normalizedCovector i v z) =
        q.covector i u z ⬝ᵥ (q.gram i z)⁻¹.mulVec (q.covector i v z) := by
  filter_upwards [q.differential i] with z hz
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  simp only [normalizedCovector,EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  rw [dotProduct_comm]
  exact (dot_mulVec_sqrt_cross _ hG.inv.posSemidef _ _).symm
end ChartGeometry
end CAT0Fillings
end

end OAI
