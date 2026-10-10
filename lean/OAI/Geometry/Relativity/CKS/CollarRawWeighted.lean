import OAI.Geometry.Relativity.CKS.CollarMomentumWeighted
import OAI.Geometry.Relativity.CKS.CollarRawCompact

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma rawMomentum_z (p : RawCollarInput) : mz (rawMomentumInput p) = rz p := rfl
lemma rawMomentum_w (p : RawCollarInput) : mw (rawMomentumInput p) = rwgt p := rfl

theorem raw_weighted_momentum {K : Set RawCollarInput} (hK : IsCompact K)
    (hreg : K ⊆ rawDomain) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ p : RawCollarInput, p ∈ Metric.cthickening δ K →
      rawOriginal p ∈ Metric.cthickening δ K →
      ∀ r A : ℝ, 1 ≤ r → rz p = 1/r → 0 ≤ rwgt p → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1 i| ≤ A*rwgt p) →
      |coordinateQ (rawMomentumInput (rawOriginal p))| ≤ B/r^3 ∧
      |coordinateQ (rawMomentumInput p)-coordinateQ (rawMomentumInput (rawOriginal p))-
        normalizedMean (rawMomentumInput p)*rwgt p/r^2| ≤ C*A*rwgt p/r^3 ∧
      |coordinateQ (rawMomentumInput p)-coordinateQ (rawMomentumInput (rawOriginal p))-
        2*rwgt p/r^2| ≤ (C*A+B)*rwgt p/r^3 ∧
      (∀ a, |coordinateZ (rawMomentumInput (rawOriginal p)) a| ≤ B/r^2) ∧
      (∀ a, |coordinateZ (rawMomentumInput p) a-
        coordinateZ (rawMomentumInput (rawOriginal p)) a| ≤ C*A*rwgt p/r^2) ∧
      |normalizedMean (rawMomentumInput p)-2| ≤ B/r^2 := by
  obtain ⟨δ,hδ,Craw,hdom,hraw,hcompact⟩ := rawMomentum_uniform hK hreg
  have hinput : rawMomentumInput '' Metric.cthickening δ K ⊆ momentumRegion := by
    rintro _ ⟨p,hp,rfl⟩
    exact (hdom hp).2.2
  obtain ⟨ε,hε,C,B,hC,hB,hest⟩ := weighted_momentum hcompact hinput
  refine ⟨δ,hδ,C*Craw,B,mul_nonneg hC Craw.coe_nonneg,hB,?_⟩
  intro p hp hp₀ r A hr hz hw hA hparams
  have hd : ‖rawMomentumInput p-rawMomentumInput (rawOriginal p)‖ ≤
      ((Craw:ℝ)*A)*rwgt p := by
    have hh := hraw.dist_le_mul p hp (rawOriginal p) hp₀
    rw [dist_eq_norm,dist_eq_norm] at hh
    exact (hh.trans (mul_le_mul_of_nonneg_left
      (rawOriginal_difference hA hw hparams) Craw.coe_nonneg)).trans_eq (by ring)
  have hp' : rawMomentumInput p ∈ Metric.cthickening ε
      (rawMomentumInput '' Metric.cthickening δ K) :=
    Metric.self_subset_cthickening _ ⟨p,hp,rfl⟩
  have hp₀' : rawMomentumInput (rawOriginal p) ∈ Metric.cthickening ε
      (rawMomentumInput '' Metric.cthickening δ K) :=
    Metric.self_subset_cthickening _ ⟨rawOriginal p,hp₀,rfl⟩
  have hh := hest (rawMomentumInput p) (rawMomentumInput (rawOriginal p)) hp' hp₀'
    r ((Craw:ℝ)*A) hr hz (by simpa only [rawMomentum_z,rawOriginal_z] using hz)
    (rawOriginal_w p) hw (mul_nonneg Craw.coe_nonneg hA) hd
  simpa only [rawMomentum_w,mul_assoc] using hh

end
end CKSAngularGeometry

end

end OAI
