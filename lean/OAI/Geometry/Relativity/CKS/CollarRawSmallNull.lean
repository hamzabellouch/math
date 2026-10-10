import OAI.Geometry.Relativity.CKS.CollarRawNull
import OAI.Geometry.Relativity.CKS.CollarNullNormalization
import OAI.Geometry.Relativity.CKS.CollarNullErrors

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma rawSmallNull_difference {p : RawNullInput} {r : ℝ}
    (hr : 0 < r) (hz : rz p.1=1/r) (hp : p ∈ rawNullDomain)
    (hp₀ : rawNullOriginal p ∈ rawNullDomain) :
    coordinateSmallNull (rawNullMap p) r-coordinateSmallNull (rawNullMap (rawNullOriginal p)) r-
      2*rwgt p.1/(r^3*Real.sqrt r) =
    (nullResidual (rawNullMap p)-nullResidual (rawNullMap (rawNullOriginal p)))/r^4-
      2*rwgt p.1*((rawD p.1).1/nullD (rawMomentumInput p.1))/(r^6*Real.sqrt r)+
      (scalarCurvature (scalarMatrixToJet (rawQ p.1))-
        scalarCurvature (scalarMatrixToJet (rawQ (rawOriginal p.1))))/(2*r^2) := by
  have hz₀ : mz (nP (rawNullMap (rawNullOriginal p))) = 1/r := by
    change rz (rawOriginal p.1) = 1/r
    rw [rawOriginal_z,hz]
  rw [coordinateSmallNull_factor hr hz (rawNullMap_regular hp),
    coordinateSmallNull_factor hr hz₀ (rawNullMap_regular hp₀)]
  have hw₀ : mw (nP (rawNullMap (rawNullOriginal p))) = 0 := rawOriginal_w p.1
  rw [hw₀]
  have hd : nullD (rawMomentumInput p.1) = 1+(1/r)^3*(rawD p.1).1 := by
    change 1+rz p.1^3*(rawD p.1).1 = _
    rw [hz]
  have hd0 : nullD (rawMomentumInput p.1) ≠ 0 := (rawNullMap_regular hp).2
  change 2*rwgt p.1/(r^3*Real.sqrt r)/nullD (rawMomentumInput p.1)+
    (scalarCurvature (scalarMatrixToJet (rawQ p.1))/2-1)/r^2+
    nullResidual (rawNullMap p)/r^4-
    (2*0/(r^3*Real.sqrt r)/nullD (rawMomentumInput (rawOriginal p.1))+
      (scalarCurvature (scalarMatrixToJet (rawQ (rawOriginal p.1)))/2-1)/r^2+
      nullResidual (rawNullMap (rawNullOriginal p))/r^4)-2*rwgt p.1/(r^3*Real.sqrt r) = _
  have hpad : 2*rwgt p.1/(r^3*Real.sqrt r)/nullD (rawMomentumInput p.1)-
      2*rwgt p.1/(r^3*Real.sqrt r) =
      -2*rwgt p.1*((rawD p.1).1/nullD (rawMomentumInput p.1))/(r^6*Real.sqrt r) := by
    rw [hd] at hd0 ⊢
    have hd1 : r^3+(rawD p.1).1 ≠ 0 := by
      intro he
      apply hd0
      field_simp [hr.ne']
      simpa using he
    field_simp [hr.ne',hd1]
    ring
  linear_combination hpad

theorem raw_weighted_small_null {K : Set RawNullInput} (hK : IsCompact K)
    (hreg : K ⊆ rawNullDomain) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : RawNullInput, p ∈ Metric.cthickening δ K →
      rawNullOriginal p ∈ Metric.cthickening δ K →
      ∀ r A : ℝ, 1 ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |coordinateSmallNull (rawNullMap p) r-coordinateSmallNull (rawNullMap (rawNullOriginal p)) r-
        2*rwgt p.1/(r^3*Real.sqrt r)| ≤ C*(A+1)*rwgt p.1/r^4 := by
  obtain ⟨δ,hδ,C,B,D,hC,hB,hD,hdom,hest⟩ := raw_null_uniform hK hreg
  refine ⟨δ,hδ,C+2*B+D,by positivity,?_⟩
  intro p hp hp₀ r A hr hz hw hA hparams
  obtain ⟨hx,hy,hz'⟩ := hest p hp hp₀ r A hr hz hw hA hparams
  have hr0 : 0 < r := by linarith
  rw [rawSmallNull_difference hr0 hz (hdom hp) (hdom hp₀)]
  apply (smallNull_remainders_bound hr hw hA hC hB hD hx hy hz').trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hr0.le 4)
  apply mul_le_mul_of_nonneg_right _ hw
  nlinarith

end
end CKSAngularGeometry

end

end OAI
