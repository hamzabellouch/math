import OAI.Geometry.Relativity.CKS.CollarRawWeighted
import OAI.Geometry.Relativity.CKS.CollarSmallNullBounded

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma raw_projected_reference_tube {K : Set MatrixScalarJet} {B δ : ℝ} {p : RawNullInput}
    (hq : rmat p.1 0 ∈ K) (hp : ‖p‖ ≤ B) (hz : |rz p.1| ≤ δ) :
    p.1 ∈ Metric.cthickening δ (nr '' rawReferenceFamily K B) ∧
    rawOriginal p.1 ∈ Metric.cthickening δ (nr '' rawReferenceFamily K B) := by
  constructor
  · exact Metric.mem_cthickening_of_dist_le p.1 (rawZeroRadius p.1) δ _
      ⟨rawNullZeroRadius p,rawNullZeroRadius_mem hq hp,rfl⟩ ((rawZeroRadius_dist p.1).trans hz)
  · exact Metric.mem_cthickening_of_dist_le (rawOriginal p.1)
      (rawZeroRadius (rawOriginal p.1)) δ _
      ⟨rawNullZeroRadius (rawNullOriginal p),
        rawNullZeroRadius_mem hq ((rawNullOriginal_norm p).trans hp),rfl⟩
      ((rawZeroRadius_dist _).trans (by simpa only [rawOriginal_z] using hz))

theorem bounded_raw_momentum {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r A : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |coordinateQ (rawMomentumInput (rawOriginal p.1))| ≤ D/r^3 ∧
      |coordinateQ (rawMomentumInput p.1)-coordinateQ (rawMomentumInput (rawOriginal p.1))-
        normalizedMean (rawMomentumInput p.1)*rwgt p.1/r^2| ≤ C*A*rwgt p.1/r^3 ∧
      |coordinateQ (rawMomentumInput p.1)-coordinateQ (rawMomentumInput (rawOriginal p.1))-
        2*rwgt p.1/r^2| ≤ (C*A+D)*rwgt p.1/r^3 ∧
      (∀ a, |coordinateZ (rawMomentumInput (rawOriginal p.1)) a| ≤ D/r^2) ∧
      (∀ a, |coordinateZ (rawMomentumInput p.1) a-
        coordinateZ (rawMomentumInput (rawOriginal p.1)) a| ≤ C*A*rwgt p.1/r^2) ∧
      |normalizedMean (rawMomentumInput p.1)-2| ≤ D/r^2 := by
  have hfamily := (rawReferenceFamily_compact hK B).image (show Continuous nr from by fun_prop)
  have hregular : nr '' rawReferenceFamily K B ⊆ rawDomain := by
    rintro _ ⟨p,hp,rfl⟩
    exact rawReferenceFamily_regular hreg B hp
  obtain ⟨δ,hδ,C,D,hC,hD,hh⟩ := raw_weighted_momentum hfamily hregular
  refine ⟨max 1 (1/δ),le_max_left _ _,C,D,hC,hD,?_⟩
  intro p hq hp r A hr hz hw hA hparams
  obtain ⟨hr1,hd⟩ := inverse_radius_threshold hδ hr
  obtain ⟨hp',hp₀'⟩ := raw_projected_reference_tube hq hp (by simpa only [hz] using hd)
  exact hh p.1 hp' hp₀' r A hr1 hz hw hA hparams

end
end CKSAngularGeometry

end

end OAI
