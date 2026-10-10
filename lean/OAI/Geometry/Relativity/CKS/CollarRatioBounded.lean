import OAI.Geometry.Relativity.CKS.CollarSmallNullBounded
import OAI.Geometry.Relativity.CKS.CollarRawRatio

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem bounded_raw_ratio {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r A : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |nullRatio (rawMomentumInput p.1)-1| ≤ D/r^2 ∧
      |nullRatio (rawMomentumInput p.1)-nullRatio (rawMomentumInput (rawOriginal p.1))| ≤
        C*A*rwgt p.1/r^3 := by
  obtain ⟨δ,hδ,C,D,hC,hD,hh⟩ := raw_ratio_uniform (rawReferenceFamily_compact hK B)
    (rawReferenceFamily_regular hreg B)
  refine ⟨max 1 (1/δ),le_max_left _ _,C,1+D,hC,by positivity,?_⟩
  intro p hq hp r A hr hz hw hA hparams
  obtain ⟨hr1,hd⟩ := inverse_radius_threshold hδ hr
  obtain ⟨hp',hp₀'⟩ := raw_reference_tube hq hp (by simpa only [hz] using hd)
  exact hh p hp' hp₀' r A hr1 hz hw hA hparams

end
end CKSAngularGeometry

end

end OAI
