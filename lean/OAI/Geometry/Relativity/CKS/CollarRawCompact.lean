import OAI.Geometry.Relativity.CKS.LogPhysicalMassJet
import OAI.Geometry.Relativity.CKS.CollarRawMomentum

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def rawDomain : Set RawCollarInput := {p | rawRegular p ∧
  rawLapseInput p ∈ lapseCoefficientRegion ∧ rawMomentumInput p ∈ momentumRegion}

lemma rawRegular_cont {p : RawCollarInput} (hp : rawRegular p) :
    ∀ᶠ q in 𝓝 p, rawRegular q := by
  have hc : ContinuousAt (fun p : RawCollarInput => determinant (fun i k => (rawQ p i k).1)) p :=
    determinant_smooth.contDiffAt.continuousAt.comp
      (by fun_prop : ContinuousAt (fun p : RawCollarInput => (fun i k => (rawQ p i k).1)) p)
  exact hc.eventually (eventually_ne_nhds hp)
lemma rawDomain_open : IsOpen rawDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hl := (rawLapseInput_smooth hp.1).continuousAt.eventually
    (lapseCoefficientRegion_open.mem_nhds hp.2.1)
  have hm := (rawMomentumInput_smooth hp.1 hp.2.1).continuousAt.eventually
    (momentumRegion_open.mem_nhds hp.2.2)
  filter_upwards [rawRegular_cont hp.1,hl,hm] with q hq hql hqm
  exact ⟨hq,hql,hqm⟩
lemma rawDomain_at_zero {p : RawCollarInput} (hz : rz p = 0)
    (hσ : determinant (fun i k => (rmat p 0 i k).1) ≠ 0) : p ∈ rawDomain := by
  have hq : rawQ p = rmat p 0 := by simp [rawQ,hz]
  have hreg : rawRegular p := by simpa [rawRegular,hq] using hσ
  have hl : rawLapseInput p ∈ lapseCoefficientRegion := by
    simpa only [rawLapseInput,hz] using lapseCoefficientRegion_zero (rawT p) (rawF p) (rawD p)
  refine ⟨hreg,hl,?_⟩
  change determinant (scalarMatrixToJet (rawQ p)).1 ≠ 0 ∧
    1+rz p^3*(rawA p).1 ≠ 0
  exact ⟨by simpa [scalarMatrixToJet,hq] using hσ,by simp [hz]⟩

lemma rawMomentum_uniform {K : Set RawCollarInput} (hK : IsCompact K)
    (hreg : K ⊆ rawDomain) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0,
      Metric.cthickening δ K ⊆ rawDomain ∧
      LipschitzOnWith C rawMomentumInput (Metric.cthickening δ K) ∧
      IsCompact (rawMomentumInput '' Metric.cthickening δ K) := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : ProperSpace RawCollarInput := FiniteDimensional.proper ℝ RawCollarInput
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open rawDomain_open hreg
  have hk := hK.cthickening (r:=δ)
  obtain ⟨C,hC⟩ : ∃ C, LipschitzOnWith C rawMomentumInput (Metric.cthickening δ K) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hk
    intro p hp
    obtain ⟨C,t,ht,hC⟩ := ((rawMomentumInput_smooth (hsub hp).1 (hsub hp).2.1).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  exact ⟨δ,hδ,C,hsub,hC,hk.image_of_continuousOn hC.continuousOn⟩

def rawOriginal (p : RawCollarInput) : RawCollarInput := (fun i => if i=0 then rz p else 0,p.2)
def rawZeroRadius (p : RawCollarInput) : RawCollarInput := (fun i => if i=0 then 0 else p.1 i,p.2)

lemma rawOriginal_z (p : RawCollarInput) : rz (rawOriginal p) = rz p := by simp [rawOriginal,rz]
lemma rawOriginal_w (p : RawCollarInput) : rwgt (rawOriginal p) = 0 := by simp [rawOriginal,rwgt,show (4:Fin 5) ≠ 0 by decide]
lemma rawZeroRadius_z (p : RawCollarInput) : rz (rawZeroRadius p) = 0 := by simp [rawZeroRadius,rz]
lemma rawZeroRadius_dist (p : RawCollarInput) : dist p (rawZeroRadius p) ≤ |rz p| := by
  rw [dist_eq_norm]
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro i
    by_cases hi : i=0
    · subst i; simp [rawZeroRadius,rz]
    · simp [rawZeroRadius,hi,abs_nonneg]
  · simp [rawZeroRadius]
lemma rawOriginal_difference {p : RawCollarInput} {A : ℝ} (hA : 0 ≤ A)
    (hw : 0 ≤ rwgt p) (h : ∀ i, i ≠ 0 → |p.1 i| ≤ A*rwgt p) :
    ‖p-rawOriginal p‖ ≤ A*rwgt p := by
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA hw)).mpr
    intro i
    by_cases hi : i=0
    · subst i; simp [rawOriginal,rz,mul_nonneg hA hw]
    · simpa [rawOriginal,hi,Real.norm_eq_abs] using h i hi
  · simp [rawOriginal,mul_nonneg hA hw]

end
end CKSAngularGeometry

end

end OAI
