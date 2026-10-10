import OAI.Geometry.Relativity.CKS.CollarRawNull
import OAI.Geometry.Relativity.CKS.CollarNullRatio

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma rawRatioResidual_smooth {p : RawNullInput} (hp : p ∈ rawNullDomain) :
    ContDiffAt ℝ ∞ (fun p => ratioResidual (rawMomentumInput p.1)) p := by
  exact (ratioResidual_smooth (rawNullMap_regular hp)).comp p
    ((rawMomentumInput_smooth hp.1 hp.2.1).comp p (by fun_prop))

lemma raw_ratio_uniform {K : Set RawNullInput} (hK : IsCompact K)
    (hreg : K ⊆ rawNullDomain) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ p : RawNullInput, p ∈ Metric.cthickening δ K →
      rawNullOriginal p ∈ Metric.cthickening δ K →
      ∀ r A : ℝ, 1 ≤ r → rz p.1 = 1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |nullRatio (rawMomentumInput p.1)-1| ≤ (1+B)/r^2 ∧
      |nullRatio (rawMomentumInput p.1)-nullRatio (rawMomentumInput (rawOriginal p.1))| ≤
        C*A*rwgt p.1/r^3 := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  obtain ⟨δ,hδ,hdom⟩ := hK.exists_cthickening_subset_open rawNullDomain_open hreg
  have hk := hK.cthickening (r:=δ)
  obtain ⟨C,hLip⟩ : ∃ C, LipschitzOnWith C (fun p => ratioResidual (rawMomentumInput p.1))
      (Metric.cthickening δ K) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hk
    intro p hp
    obtain ⟨C,t,ht,hC⟩ := ((rawRatioResidual_smooth (hdom hp)).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  obtain ⟨B,hB⟩ := hk.exists_bound_of_continuousOn
    (fun p hp => (rawRatioResidual_smooth (hdom hp)).continuousAt.continuousWithinAt)
  refine ⟨δ,hδ,C,max B 0,C.coe_nonneg,le_max_right _ _,?_⟩
  intro p hp hp₀ r A hr hz hw hA hparams
  refine ⟨nullRatio_bound (rawNullMap_regular (hdom hp)) hr hz
    (le_max_right _ _) ((hB p hp).trans (le_max_left _ _)),?_⟩
  have he : mz (rawMomentumInput p.1) = mz (rawMomentumInput (rawOriginal p.1)) :=
    (rawOriginal_z p.1).symm
  erw [nullRatio_difference (rawNullMap_regular (hdom hp))
    (rawNullMap_regular (hdom hp₀)) he]
  have hz' : mz (rawMomentumInput p.1) = 1/r := hz
  erw [hz',abs_mul,abs_of_nonneg (by positivity : 0 ≤ (1/r)^3)]
  have hh := hLip.dist_le_mul p hp (rawNullOriginal p) hp₀
  rw [dist_eq_norm,dist_eq_norm] at hh
  have hb := hh.trans (mul_le_mul_of_nonneg_left (rawNullOriginal_diff hA hw hparams) C.coe_nonneg)
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (1/r)^3)).trans_eq (by ring)

end
end CKSAngularGeometry

end

end OAI
