import OAI.Geometry.Relativity.CKS.CollarRawSmallNull
import OAI.Geometry.Relativity.CKS.CollarRawFamily

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma inverse_radius_threshold {δ r : ℝ} (hδ : 0 < δ) (hr : max 1 (1/δ) ≤ r) :
    1 ≤ r ∧ |1/r| ≤ δ := by
  have hr1 := (le_max_left 1 (1/δ)).trans hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  refine ⟨hr1,?_⟩
  rw [abs_of_pos (one_div_pos.mpr hr0)]
  apply (div_le_iff₀ hr0).mpr
  simpa only [mul_comm] using ((div_le_iff₀ hδ).mp ((le_max_right _ _).trans hr))

theorem bounded_raw_small_null {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r A : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |coordinateSmallNull (rawNullMap p) r-coordinateSmallNull (rawNullMap (rawNullOriginal p)) r-
        2*rwgt p.1/(r^3*Real.sqrt r)| ≤ C*(A+1)*rwgt p.1/r^4 := by
  obtain ⟨δ,hδ,C,hC,hh⟩ := raw_weighted_small_null (rawReferenceFamily_compact hK B)
    (rawReferenceFamily_regular hreg B)
  refine ⟨max 1 (1/δ),le_max_left _ _,C,hC,?_⟩
  intro p hq hp r A hr hz hw hA hparams
  obtain ⟨hr1,hd⟩ := inverse_radius_threshold hδ hr
  obtain ⟨hp',hp₀'⟩ := raw_reference_tube hq hp (by simpa only [hz] using hd)
  exact hh p hp' hp₀' r A hr1 hz hw hA hparams

end
end CKSAngularGeometry

end

end OAI
