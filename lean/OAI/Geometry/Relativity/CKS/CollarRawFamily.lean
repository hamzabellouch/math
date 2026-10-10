import OAI.Geometry.Relativity.CKS.CollarRawNull

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def rawNullZeroRadius (p : RawNullInput) : RawNullInput := (rawZeroRadius p.1,p.2)
def rawReferenceFamily (K : Set MatrixScalarJet) (B : ℝ) : Set RawNullInput :=
  {p | rmat p.1 0 ∈ K ∧ rz p.1 = 0} ∩ Metric.closedBall 0 B
lemma rawReferenceFamily_compact {K : Set MatrixScalarJet} (hK : IsCompact K) (B : ℝ) :
    IsCompact (rawReferenceFamily K B) := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  exact (isCompact_closedBall (0:RawNullInput) B).inter_left
    ((hK.isClosed.preimage (by fun_prop)).inter (isClosed_eq (by fun_prop) continuous_const))
lemma rawReferenceFamily_regular {K : Set MatrixScalarJet}
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B : ℝ) :
    rawReferenceFamily K B ⊆ rawNullDomain := by
  intro p hp
  exact rawDomain_at_zero hp.1.2 (hreg _ hp.1.1)

lemma rawOriginal_norm (p : RawCollarInput) : ‖rawOriginal p‖ ≤ ‖p‖ := by
  apply norm_prod_le_iff.mpr
  refine ⟨?_,?_⟩
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    by_cases hi : i=0
    · subst i
      exact (norm_le_pi_norm p.1 0).trans (norm_fst_le p)
    · simp only [rawOriginal,hi,ite_false,norm_zero]
      exact norm_nonneg p
  · exact norm_snd_le p
lemma rawZeroRadius_norm (p : RawCollarInput) : ‖rawZeroRadius p‖ ≤ ‖p‖ := by
  apply norm_prod_le_iff.mpr
  refine ⟨?_,norm_snd_le p⟩
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  by_cases hi : i=0
  · simp only [rawZeroRadius,hi,ite_true,norm_zero]
    exact norm_nonneg p
  · simp only [rawZeroRadius,hi,ite_false]
    exact (norm_le_pi_norm p.1 i).trans (norm_fst_le p)
lemma rawNullOriginal_norm (p : RawNullInput) : ‖rawNullOriginal p‖ ≤ ‖p‖ :=
  norm_prod_le_iff.mpr ⟨(rawOriginal_norm p.1).trans (norm_fst_le p),norm_snd_le p⟩
lemma rawNullZeroRadius_norm (p : RawNullInput) : ‖rawNullZeroRadius p‖ ≤ ‖p‖ :=
  norm_prod_le_iff.mpr ⟨(rawZeroRadius_norm p.1).trans (norm_fst_le p),norm_snd_le p⟩
lemma rawNullZeroRadius_close (p : RawNullInput) :
    dist p (rawNullZeroRadius p) ≤ |rz p.1| := by
  change max (dist p.1 (rawZeroRadius p.1)) (dist p.2 p.2) ≤ _
  rw [max_le_iff,dist_self]
  exact ⟨rawZeroRadius_dist p.1,abs_nonneg _⟩
lemma rawNullZeroRadius_mem {K : Set MatrixScalarJet} {B : ℝ} {p : RawNullInput}
    (hq : rmat p.1 0 ∈ K) (hp : ‖p‖ ≤ B) :
    rawNullZeroRadius p ∈ rawReferenceFamily K B := by
  refine ⟨⟨hq,rawZeroRadius_z _⟩,?_⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using (rawNullZeroRadius_norm p).trans hp
lemma raw_reference_tube {K : Set MatrixScalarJet} {B δ : ℝ} {p : RawNullInput}
    (hq : rmat p.1 0 ∈ K) (hp : ‖p‖ ≤ B) (hz : |rz p.1| ≤ δ) :
    p ∈ Metric.cthickening δ (rawReferenceFamily K B) ∧
    rawNullOriginal p ∈ Metric.cthickening δ (rawReferenceFamily K B) := by
  constructor
  · exact Metric.mem_cthickening_of_dist_le p (rawNullZeroRadius p) δ _
      (rawNullZeroRadius_mem hq hp) ((rawNullZeroRadius_close p).trans hz)
  · apply Metric.mem_cthickening_of_dist_le (rawNullOriginal p)
      (rawNullZeroRadius (rawNullOriginal p)) δ _
      (rawNullZeroRadius_mem hq ((rawNullOriginal_norm p).trans hp))
    exact (rawNullZeroRadius_close _).trans (by simpa only [rawNullOriginal,rawOriginal_z] using hz)

end
end CKSAngularGeometry

end

end OAI
