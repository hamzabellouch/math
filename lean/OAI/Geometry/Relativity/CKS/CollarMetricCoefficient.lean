import OAI.Geometry.Relativity.CKS.CollarAngularWeighted
import OAI.Geometry.Relativity.CKS.CovariantHeat

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

 def normalizedFoliationMetric (z U : ℝ) (q : Mat) (S : Point) : AmbientMat :=
  metricBlock (1/U^2+z^6*(1+z^2)*(∑ a, ∑ b, q a b*S a*S b))
    (fun a => z^3*Real.sqrt (1+z^2)*(∑ b, q a b*S b)) q

 def metricCorrection (z A : ℝ) (q m : Mat) (S : Point) : AmbientMat :=
  metricBlock (-A*(2+z^3*A)/(1+z^3*A)^2+z^3*(1+z^2)*(∑ a, ∑ b, q a b*S a*S b))
    (fun a => Real.sqrt (1+z^2)*(∑ b, q a b*S b)) m

lemma metric_correction_identity {z A : ℝ} (hA : 1+z^3*A ≠ 0) (σ m : Mat) (S : Point) :
    normalizedFoliationMetric z (1+z^3*A) (σ+z^3 • m) S-
      metricBlock 1 0 σ = z^3 • metricCorrection z A (σ+z^3 • m) m S := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [normalizedFoliationMetric,metricCorrection,metricBlock,Matrix.of_apply,
      Matrix.sub_apply,Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
      Matrix.head_fin_const,Pi.zero_apply]
  all_goals field_simp
  all_goals ring

 def rawNormalizedSpeed (p : RawNullInput) : ℝ := 1+rz p.1^3*(rawA p.1).1
 def rawMetricDomain : Set RawNullInput := rawNullDomain ∩ {p | rawNormalizedSpeed p ≠ 0}
 def rawMetricCorrection (p : RawNullInput) : AmbientMat :=
  metricCorrection (rz p.1) (rawA p.1).1 (rawAngularMatrix p)
    (fun a b => (1-re p.1)*(rmat p.1 1 a b).1)
    (fun a => (rawS p.1 a).1)
 def rawNormalizedMetric (p : RawNullInput) : AmbientMat :=
  normalizedFoliationMetric (rz p.1) (rawNormalizedSpeed p) (rawAngularMatrix p)
    (fun a => (rawS p.1 a).1)
 def rawBackgroundMetric (p : RawNullInput) : AmbientMat :=
  metricBlock 1 0 (fun a b => (rmat p.1 0 a b).1)

lemma rawNormalizedSpeed_smooth {p : RawNullInput} (hp : p ∈ rawNullDomain) :
    ContDiffAt ℝ ∞ rawNormalizedSpeed p := by
  have ha := ((rawA_smooth hp.1 hp.2.1).fst).comp p
    (by fun_prop : ContDiffAt ℝ ∞ (Prod.fst : RawNullInput → RawCollarInput) p)
  exact contDiffAt_const.add ((by fun_prop : ContDiffAt ℝ ∞ (fun p : RawNullInput => rz p.1^3) p).mul ha)

lemma rawMetricDomain_open : IsOpen rawMetricDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hn := (rawNormalizedSpeed_smooth hp.1).continuousAt.eventually
    (isOpen_ne.mem_nhds hp.2)
  filter_upwards [rawNullDomain_open.mem_nhds hp.1,hn] with q hq hqn
  exact ⟨hq,hqn⟩

lemma rawMetricFamily_regular {K : Set MatrixScalarJet}
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B : ℝ) :
    rawReferenceFamily K B ⊆ rawMetricDomain := by
  intro p hp
  refine ⟨rawReferenceFamily_regular hreg B hp,?_⟩
  change 1+rz p.1^3*(rawA p.1).1 ≠ 0
  rw [hp.1.2]
  norm_num

lemma rawMetricCorrection_continuousAt {p : RawNullInput} (hp : p ∈ rawMetricDomain) :
    ContinuousAt rawMetricCorrection p := by
  have ha := ((rawA_smooth hp.1.1 hp.1.2.1).fst).continuousAt.comp
    (continuous_fst.continuousAt : ContinuousAt (Prod.fst : RawNullInput → RawCollarInput) p)
  have hU := (rawNormalizedSpeed_smooth hp.1).continuousAt
  have hq := rawAngularMatrix_smooth.continuous.continuousAt (x:=p)
  have hS : Continuous (fun p : RawNullInput => fun a => (rawS p.1 a).1) := by
    unfold rawS; fun_prop
  have hm : Continuous (fun p : RawNullInput => fun a b => (1-re p.1)*(rmat p.1 1 a b).1) := by fun_prop
  have hz : Continuous (fun p : RawNullInput => rz p.1) := by fun_prop
  have hs : Continuous (fun p : RawNullInput => Real.sqrt (1+rz p.1^2)) := by fun_prop
  apply continuousAt_pi.mpr; intro i
  apply continuousAt_pi.mpr; intro j
  fin_cases i <;> fin_cases j <;>
    simp only [rawMetricCorrection,metricCorrection,metricBlock,Matrix.of_apply]
  · exact ((ha.neg.mul (continuousAt_const.add ((hz.continuousAt.pow 3).mul ha))).div
      (hU.pow 2) (pow_ne_zero 2 hp.2)).add
      (((hz.continuousAt.pow 3).mul (continuousAt_const.add (hz.continuousAt.pow 2))).mul
        (tendsto_finsetSum _ (fun a _ => tendsto_finsetSum _ (fun b _ =>
          ((continuousAt_pi.mp (continuousAt_pi.mp hq a) b).mul ((continuous_pi_iff.mp hS a).continuousAt)).mul
            ((continuous_pi_iff.mp hS b).continuousAt)))))
  all_goals first
  | exact hs.continuousAt.mul (tendsto_finsetSum _ (fun b _ =>
      (continuousAt_pi.mp (continuousAt_pi.mp hq _) b).mul ((continuous_pi_iff.mp hS b).continuousAt)))
  | exact (continuous_pi_iff.mp (continuous_pi_iff.mp hm _) _).continuousAt

lemma raw_metric_correction {p : RawNullInput} (hp : p ∈ rawMetricDomain) :
    rawNormalizedMetric p-rawBackgroundMetric p=rz p.1^3 • rawMetricCorrection p := by
  have hq : rawAngularMatrix p=(fun a b => (rmat p.1 0 a b).1)+rz p.1^3 •
      (fun a b => (1-re p.1)*(rmat p.1 1 a b).1) := by
    ext a b
    simp only [rawAngularMatrix,rawQ,Matrix.add_apply,Matrix.smul_apply,Pi.add_apply,Pi.smul_apply,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
    ring
  unfold rawNormalizedMetric rawBackgroundMetric rawMetricCorrection rawNormalizedSpeed
  rw [hq]
  exact metric_correction_identity hp.2 _ _ _

theorem bounded_raw_collar_metric {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r : ℝ, R₀ ≤ r → rz p.1=1/r →
      p ∈ rawMetricDomain ∧ ‖rawNormalizedMetric p-rawBackgroundMetric p‖ ≤ C/r^3 := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  have hk := rawReferenceFamily_compact hK B
  obtain ⟨δ,hδ,hdom⟩ := hk.exists_cthickening_subset_open rawMetricDomain_open
    (rawMetricFamily_regular hreg B)
  obtain ⟨M,hM⟩ := (hk.cthickening (r:=δ)).exists_bound_of_continuousOn
    (fun p hp => (rawMetricCorrection_continuousAt (hdom hp)).continuousWithinAt)
  refine ⟨max 1 (1/δ),le_max_left _ _,max M 0,le_max_right _ _,?_⟩
  intro p hq hp r hr hz
  obtain ⟨hr1,hd⟩ := inverse_radius_threshold hδ hr
  obtain ⟨ht,_⟩ := raw_reference_tube hq hp (show |rz p.1| ≤ δ by rw [hz]; exact hd)
  refine ⟨hdom ht,?_⟩
  rw [raw_metric_correction (hdom ht),norm_smul,hz,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (1/r)^3)]
  calc
    (1/r)^3*‖rawMetricCorrection p‖ ≤ (1/r)^3*max M 0 :=
      mul_le_mul_of_nonneg_left ((hM p ht).trans (le_max_left _ _)) (by positivity)
    _ = max M 0/r^3 := by ring

end
end CKSAngularGeometry

end

end OAI
