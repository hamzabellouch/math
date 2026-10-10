import OAI.Geometry.Relativity.CKS.CollarSmallNullBounded
import OAI.Geometry.Relativity.CKS.CollarAngularNorm

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise InnerProductSpace

def commonAngularMomentum (p : MomentumInput) : AngularEuclidean :=
  mz p • covectorEmbedding (mq p).1 (coordinateZ p)

def rawAngularMatrix (p : RawNullInput) : Mat := fun i k => (rawQ p.1 i k).1

def rawAngularResidual (p : RawNullInput) : AngularEuclidean :=
  covectorEmbedding (rawAngularMatrix p) (angularResidual (rawMomentumInput p.1))

def rawPositiveDomain : Set RawNullInput := rawNullDomain ∩ {p | positiveAngular (rawAngularMatrix p)}

lemma rawAngularMatrix_smooth : ContDiff ℝ ∞ rawAngularMatrix := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro k
  exact contDiff_fst.comp ((contDiff_pi.mp (contDiff_pi.mp rawQ_smooth i) k).comp (by fun_prop))

lemma rawPositiveDomain_open : IsOpen rawPositiveDomain := by
  apply rawNullDomain_open.inter
  apply IsOpen.inter
  · exact isOpen_lt continuous_const ((continuous_apply 1).comp ((continuous_apply 1).comp rawAngularMatrix_smooth.continuous))
  · exact isOpen_lt continuous_const (determinant_smooth.continuous.comp rawAngularMatrix_smooth.continuous)

lemma rawAngularResidual_smooth {p : RawNullInput} (hp : p ∈ rawPositiveDomain) :
    ContDiffAt ℝ ∞ rawAngularResidual p := by
  have hm := (rawMomentumInput_smooth hp.1.1 hp.1.2.1).comp p
    (by fun_prop : ContDiffAt ℝ ∞ nr p)
  have hz := (contDiffAt_snd.comp _ (momentumResidual_smooth hp.1.2.2)).comp p hm
  have he : ContDiffAt ℝ ∞ (fun x : Mat × Point => covectorEmbedding x.1 x.2)
      (rawAngularMatrix p,angularResidual (rawMomentumInput p.1)) := covectorEmbedding_smooth hp.2
  change ContDiffAt ℝ ∞ ((fun x : Mat × Point => covectorEmbedding x.1 x.2) ∘
    (fun p : RawNullInput => (rawAngularMatrix p,angularResidual (rawMomentumInput p.1)))) p
  exact he.comp p (rawAngularMatrix_smooth.contDiffAt.prodMk hz)

lemma commonAngularMomentum_factor {p : MomentumInput} (hz : mz p ≠ 0) :
    commonAngularMomentum p = mz p^3 • covectorEmbedding (mq p).1 (angularResidual p) := by
  have he : coordinateZ p = mz p^2 • angularResidual p := funext fun a => coordinateZ_factor hz a
  rw [commonAngularMomentum,he,covectorEmbedding_linear,smul_smul]
  congr 1
  ring

lemma rawPositiveFamily_regular {K : Set MatrixScalarJet}
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) (B : ℝ) :
    rawReferenceFamily K B ⊆ rawPositiveDomain := by
  intro p hp
  refine ⟨rawReferenceFamily_regular (fun q hq => (hreg q hq).2.ne') B hp,?_⟩
  have he : rawAngularMatrix p = fun i k => (rmat p.1 0 i k).1 := by
    change (fun i k => ((rmat p.1 0 + (rz p.1^3*(1-re p.1)) • rmat p.1 1) i k).1) = _
    rw [hp.1.2]
    simp only [zero_pow (by decide : 3 ≠ 0),zero_mul,zero_smul,add_zero]
  change positiveAngular (rawAngularMatrix p)
  rw [he]
  exact hreg _ hp.1.1

theorem bounded_raw_common_angular {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r A : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 → 0 ≤ A →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      positiveAngular (rawAngularMatrix p) ∧ positiveAngular (rawAngularMatrix (rawNullOriginal p)) ∧
      ‖commonAngularMomentum (rawMomentumInput p.1)-
        commonAngularMomentum (rawMomentumInput (rawOriginal p.1))‖ ≤ C*A*rwgt p.1/r^3 := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  have hk := rawReferenceFamily_compact hK B
  obtain ⟨δ,hδ,hdom⟩ := hk.exists_cthickening_subset_open rawPositiveDomain_open (rawPositiveFamily_regular hreg B)
  obtain ⟨C,hLip⟩ : ∃ C, LipschitzOnWith C rawAngularResidual
      (Metric.cthickening δ (rawReferenceFamily K B)) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hk.cthickening (r:=δ))
    intro p hp
    obtain ⟨C,t,ht,hC⟩ := ((rawAngularResidual_smooth (hdom hp)).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  refine ⟨max 1 (1/δ),le_max_left _ _,C,C.coe_nonneg,?_⟩
  intro p hq hp r A hr hz hw hA hparams
  obtain ⟨hr1,hd⟩ := inverse_radius_threshold hδ hr
  obtain ⟨hp',hp₀'⟩ := raw_reference_tube hq hp (by simpa only [hz] using hd)
  refine ⟨(hdom hp').2,(hdom hp₀').2,?_⟩
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hz₁ : mz (rawMomentumInput p.1)=1/r := hz
  have hz₀ : mz (rawMomentumInput (rawOriginal p.1))=1/r := (rawOriginal_z p.1).trans hz
  rw [commonAngularMomentum_factor (by rw [hz₁]; positivity),
    commonAngularMomentum_factor (by rw [hz₀]; positivity),hz₁,hz₀,← smul_sub,norm_smul]
  change ‖(1/r)^3‖*‖rawAngularResidual p-rawAngularResidual (rawNullOriginal p)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (1/r)^3)]
  have hh := hLip.dist_le_mul p hp' (rawNullOriginal p) hp₀'
  rw [dist_eq_norm,dist_eq_norm] at hh
  have hb := hh.trans (mul_le_mul_of_nonneg_left (rawNullOriginal_diff hA hw hparams) C.coe_nonneg)
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (1/r)^3)).trans_eq (by ring)

end
end CKSAngularGeometry

end

end OAI
