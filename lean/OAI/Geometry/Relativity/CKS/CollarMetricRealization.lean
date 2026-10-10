import OAI.Geometry.Relativity.CKS.CollarFieldRegion
import OAI.Geometry.Relativity.CKS.SourcePhysicalTensor
import OAI.Geometry.Relativity.CKS.CollarMetricCoefficient

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

 def radialScale (r : ℝ) : Fin 3 → ℝ := ![Real.sqrt (1+r^2),1/r,1/r]
 def radialNormalize (r : ℝ) (G : AmbientMat) : AmbientMat :=
  fun i j => radialScale r i*G i j*radialScale r j

lemma radialNormalize_foliation {r U : ℝ} (hr : 0<r) (hU : U ≠ 0) (q : Mat) (S : Point) :
    radialNormalize r (foliationMetric (Real.sqrt (1+r^2)*U) (r^2 • q) ((1/r)^5 • S))=
      normalizedFoliationMetric (1/r) U q S := by
  have hr0 := hr.ne'
  have hi : 1+r^2 = r^2*(1+(1/r)^2) := by field_simp; ring
  have hs : Real.sqrt (1+r^2)=r*Real.sqrt (1+(1/r)^2) := by
    conv_lhs => rw [hi,Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq hr.le]
  have hs0 : Real.sqrt (1+(1/r)^2) ≠ 0 := by positivity
  have hsq : Real.sqrt (1+(1/r)^2)^2=1+(1/r)^2 := Real.sq_sqrt (by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radialNormalize,radialScale,foliationMetric,normalizedFoliationMetric,
      metricBlock,Matrix.of_apply,Fin.sum_univ_two,hs]
  all_goals field_simp
  all_goals try rw [Real.sq_sqrt (show 0 ≤ (r^2+1)/r^2 by positivity)]
  all_goals field_simp

 def fieldNormalizedMetric (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point) : AmbientMat :=
  normalizedFoliationMetric (b 0) (fieldNormalizedLapse b f x) (fieldQ b f x) (fieldS b f x)

lemma thinNormalizedMetric (p : RawNullInput) :
    rawNormalizedMetric (thinRaw p)=rawNormalizedMetric p := by
  unfold rawNormalizedMetric rawNormalizedSpeed
  rw [thinA]
  rfl

lemma fieldNormalizedMetric_raw (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point}
    (hf : f.RegularAt x)
    (hp : rawRegular (fieldRaw b f x).1 ∧ rawLapseInput (fieldRaw b f x).1 ∈ lapseCoefficientRegion) :
    fieldNormalizedMetric b f x=rawNormalizedMetric (fieldRaw b f x) := by
  obtain ⟨h0,hr,hd⟩ := field_primitive_regular b hf hp
  have hU := congrArg Prod.fst (field_normalizedLapse_jet b hf h0 hr hd)
  change fieldNormalizedLapse b f x=1+b 0^3*(rawA (fieldRaw b f x).1).1 at hU
  unfold fieldNormalizedMetric rawNormalizedMetric rawNormalizedSpeed
  rw [hU,field_angular_matrix b hf]
  rfl

theorem bounded_thin_collar_metric {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
        f.RegularAt x → matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
        ∀ r : ℝ, R₀ ≤ r → b 0=1/r →
        ‖fieldNormalizedMetric b f x-metricBlock 1 0 (f.metric 0 x)‖ ≤ C/r^3 := by
  obtain ⟨R₀,hR,C,hC,hbound⟩ := bounded_raw_collar_metric hK hreg B
  refine ⟨R₀,hR,C,hC,?_⟩
  intro b f x hf hq hb hboundf r hr hz
  obtain ⟨hdom,hest⟩ := hbound (thinRaw (fieldRaw b f x)) hq
    (fieldRaw_thin_norm hB hb hboundf) r hr hz
  have hprim := (thinRaw_primitive_regular (fieldRaw b f x)).mp ⟨hdom.1.1,hdom.1.2.1⟩
  rw [fieldNormalizedMetric_raw b hf hprim,← thinNormalizedMetric]
  exact hest

end
end CKSAngularGeometry

end

end OAI
