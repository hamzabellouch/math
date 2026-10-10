import OAI.Geometry.Relativity.CKS.CollarNullMap
import OAI.Geometry.Relativity.CKS.CollarRawCurvature

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev RawNullInput := RawCollarInput × ℝ × ℝ
abbrev nr (p : RawNullInput) := p.1

def rawNullMap (p : RawNullInput) : NullInput :=
  (rawMomentumInput p.1,rawF p.1,(1-re p.1)*p.2.1-rθ p.1*p.2.2)
def rawNullOriginal (p : RawNullInput) : RawNullInput := (rawOriginal p.1,p.2)
def rawNullDomain : Set RawNullInput := nr ⁻¹' rawDomain
lemma rawNullDomain_open : IsOpen rawNullDomain := rawDomain_open.preimage (by fun_prop)

lemma rawNullMap_regular {p : RawNullInput} (hp : p ∈ rawNullDomain) :
    rawNullMap p ∈ nullRegion := by
  refine ⟨hp.2.2,?_⟩
  exact hp.2.1.2
lemma rawNullMap_smooth {p : RawNullInput} (hp : p ∈ rawNullDomain) :
    ContDiffAt ℝ ∞ rawNullMap p := by
  have hm := (rawMomentumInput_smooth hp.1 hp.2.1).comp p
    (by fun_prop : ContDiffAt ℝ ∞ nr p)
  have hf := rawF_smooth.contDiffAt.comp p (by fun_prop : ContDiffAt ℝ ∞ nr p)
  exact hm.prodMk (hf.prodMk (by fun_prop))

lemma rawNullResidual_smooth {p : RawNullInput} (hp : p ∈ rawNullDomain) :
    ContDiffAt ℝ ∞ (fun p => nullResidual (rawNullMap p)) p := by
  have h0 := nullResidual_smooth (rawNullMap_regular hp)
  exact h0.comp p (rawNullMap_smooth hp)
lemma rawNullPadding_smooth {p : RawNullInput} (hp : p ∈ rawNullDomain) :
    ContDiffAt ℝ ∞ (fun p => (rawD p.1).1/nullD (rawMomentumInput p.1)) p := by
  have hD := contDiffAt_fst.comp p ((rawD_smooth hp.1).comp p
    (by fun_prop : ContDiffAt ℝ ∞ nr p))
  have hM := (rawMomentumInput_smooth hp.1 hp.2.1).comp p
    (by fun_prop : ContDiffAt ℝ ∞ nr p)
  exact hD.div (nullD_smooth.contDiffAt.comp p hM) (rawNullMap_regular hp).2

lemma rawNullOriginal_diff {p : RawNullInput} {A : ℝ} (hA : 0 ≤ A)
    (hw : 0 ≤ rwgt p.1) (hparams : ∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) :
    ‖p-rawNullOriginal p‖ ≤ A*rwgt p.1 := by
  apply norm_prod_le_iff.mpr
  refine ⟨rawOriginal_difference hA hw hparams,?_⟩
  change ‖p.2-p.2‖ ≤ _
  rw [sub_self,norm_zero]
  exact mul_nonneg hA hw

theorem raw_null_uniform {K : Set RawNullInput} (hK : IsCompact K)
    (hreg : K ⊆ rawNullDomain) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C B D : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ 0 ≤ D ∧
      Metric.cthickening δ K ⊆ rawNullDomain ∧
      ∀ p : RawNullInput, p ∈ Metric.cthickening δ K →
      rawNullOriginal p ∈ Metric.cthickening δ K →
      ∀ r A : ℝ, 1 ≤ r → rz p.1 = 1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |nullResidual (rawNullMap p)-nullResidual (rawNullMap (rawNullOriginal p))| ≤ C*A*rwgt p.1 ∧
      |(rawD p.1).1/nullD (rawMomentumInput p.1)| ≤ B ∧
      |scalarCurvature (scalarMatrixToJet (rawQ p.1))-
        scalarCurvature (scalarMatrixToJet (rawQ (rawOriginal p.1)))| ≤ D*A*rwgt p.1/r^3 := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  have hKp := hK.image (show Continuous nr from by fun_prop)
  have hKpreg : nr '' K ⊆ rawDomain := by rintro _ ⟨p,hp,rfl⟩; exact hreg hp
  obtain ⟨ε,hε,D,hD,hcurv⟩ := raw_curvature_uniform hKp hKpreg
  let U : Set RawNullInput := rawNullDomain ∩ nr ⁻¹' Metric.thickening ε (nr '' K)
  have hopen : IsOpen U := rawNullDomain_open.inter
    ((Metric.isOpen_thickening).preimage (by fun_prop : Continuous nr))
  have hKU : K ⊆ U := by
    intro p hp
    exact ⟨hreg hp,Metric.self_subset_thickening hε (nr '' K) ⟨p,hp,rfl⟩⟩
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open hopen hKU
  have hdom : Metric.cthickening δ K ⊆ rawNullDomain := fun _ hp => (hsub hp).1
  have hk := hK.cthickening (r:=δ)
  obtain ⟨C,hLip⟩ : ∃ C, LipschitzOnWith C (fun p => nullResidual (rawNullMap p))
      (Metric.cthickening δ K) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hk
    intro p hp
    obtain ⟨C,t,ht,hC⟩ := ((rawNullResidual_smooth (hdom hp)).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  obtain ⟨B,hB⟩ := hk.exists_bound_of_continuousOn
    (fun p hp => (rawNullPadding_smooth (hdom hp)).continuousAt.continuousWithinAt)
  refine ⟨δ,hδ,C,max B 0,D,C.coe_nonneg,le_max_right _ _,hD,hdom,?_⟩
  intro p hp hp₀ r A hr hz hw hA hparams
  constructor
  · have hh := hLip.dist_le_mul p hp (rawNullOriginal p) hp₀
    rw [dist_eq_norm,dist_eq_norm] at hh
    exact (hh.trans (mul_le_mul_of_nonneg_left
      (rawNullOriginal_diff hA hw hparams) C.coe_nonneg)).trans_eq (by ring)
  constructor
  · exact (hB p hp).trans (le_max_left _ _)
  · apply hcurv p.1
      (Metric.thickening_subset_cthickening ε (nr '' K) (hsub hp).2)
      (Metric.thickening_subset_cthickening ε (nr '' K) (hsub hp₀).2)
      r A hr hz hw hA
    exact hparams 1 (by decide)

end
end CKSAngularGeometry

end

end OAI
