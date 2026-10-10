import Mathlib
import OAI.Analysis.HardSphere.Geometry.ScalarNormSqIntegral
import OAI.Analysis.HardSphere.Rescaling.PhysicalRescaling

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Rescaling
attribute [local instance] Classical.propDecidable

def amplitude (N : ℕ) (L J : Length) : ℝ := Real.sqrt ((jacobian N L J)⁻¹)
lemma amplitude_pos (N : ℕ) (L J : Length) : 0<amplitude N L J :=
  Real.sqrt_pos.mpr (inv_pos.mpr (jacobian_pos N L J))
lemma amplitude_sq (N : ℕ) (L J : Length) : (amplitude N L J)^2=(jacobian N L J)⁻¹ :=
  Real.sq_sqrt (inv_nonneg.mpr (jacobian_pos N L J).le)

def changeMeasure (N : ℕ) (L J : Length) :
    ScalarL2 N J →L[ℝ] Lp ℂ 2 (ENNReal.ofReal (jacobian N L J) • (volume : Measure (Configuration N J))) :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top le_rfl

def rawPull (N : ℕ) (L J : Length) : ScalarL2 N J →L[ℝ] ScalarL2 N L :=
  (Lp.compMeasurePreservingₗᵢ ℝ (config N L J) (config_preserving N L J)).toContinuousLinearMap.comp
    (changeMeasure N L J)

def pull (N : ℕ) (L J : Length) : ScalarL2 N J →L[ℝ] ScalarL2 N L :=
  amplitude N L J • rawPull N L J

lemma rawPull_ae (N : ℕ) (L J : Length) (f : ScalarL2 N J) :
    (rawPull N L J f : Configuration N L → ℂ)=ᵐ[volume] fun X ↦ f (config N L J X) := by
  have ha := Lp.coeFn_compMeasurePreserving (changeMeasure N L J f) (config_preserving N L J)
  have hb := (config_preserving N L J).quasiMeasurePreserving.tendsto_ae.eventually (Lp.coeFn_LpToLpOfMeasureLeSMul
    (E:=ℂ) (p:=2) ENNReal.ofReal_ne_top (le_refl (ENNReal.ofReal (jacobian N L J) • (volume : Measure (Configuration N J)))) f)
  exact ha.trans hb
lemma pull_ae (N : ℕ) (L J : Length) (f : ScalarL2 N J) :
    (pull N L J f : Configuration N L → ℂ)=ᵐ[volume] fun X ↦ amplitude N L J • f (config N L J X) := by
  exact (Lp.coeFn_smul _ _).trans ((rawPull_ae N L J f).fun_comp fun z ↦ amplitude N L J • z)

lemma config_embedding (N : ℕ) (L J : Length) : MeasurableEmbedding (config N L J) :=
  (configHomeo N L J).measurableEmbedding

lemma pull_norm (N : ℕ) (L J : Length) (f : ScalarL2 N J) : ‖pull N L J f‖=‖f‖ := by
  have he : ‖pull N L J f‖^2=‖f‖^2 := by
    rw [scalar_norm_sq_integral]
    calc
      _ = ∫X,‖amplitude N L J • f (config N L J X)‖^2 :=
        integral_congr_ae ((pull_ae N L J f).fun_comp fun z ↦ ‖z‖^2)
      _ = (amplitude N L J)^2 * ∫X,‖f (config N L J X)‖^2 := by
        simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
      _ = (amplitude N L J)^2 * ((jacobian N L J) * ∫X,‖f X‖^2) := by
        rw [(config_preserving N L J).integral_comp (config_embedding N L J) (fun X ↦ ‖f X‖^2),integral_smul_measure,
          ENNReal.toReal_ofReal (jacobian_pos N L J).le,smul_eq_mul]
      _ = ‖f‖^2 := by rw [amplitude_sq,←mul_assoc,inv_mul_cancel₀ (jacobian_pos N L J).ne',one_mul,←scalar_norm_sq_integral]
  nlinarith [norm_nonneg (pull N L J f),norm_nonneg f]

def jet (N : ℕ) (L J : Length) : Jet N J →L[ℝ] Jet N L :=
  ((pull N L J).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (ContinuousLinearMap.pi fun p ↦ (J.val/L.val) •
      ((pull N L J).comp ((ContinuousLinearMap.proj p).comp (ContinuousLinearMap.snd ℝ _ _))))

lemma jet_fst (N : ℕ) (L J : Length) (u : Jet N J) : (jet N L J u).1=pull N L J u.1 := rfl
lemma jet_snd (N : ℕ) (L J : Length) (u : Jet N J) (p : Direction N) :
    (jet N L J u).2 p=(J.val/L.val) • pull N L J (u.2 p) := rfl
lemma jet_energy (N : ℕ) (L J : Length) (u : Jet N J) :
    energy (jet N L J u)=(J.val/L.val)^2*energy u := by
  unfold energy
  simp only [jet_snd,norm_smul,pull_norm,Real.norm_eq_abs,mul_pow,sq_abs,Finset.mul_sum]

lemma pull_bosonic {N : ℕ} {L J : Length} {f : ScalarL2 N J} (hf : bosonic f) :
    bosonic (pull N L J f) := by
  intro σ
  have hσ := (measurePreserving_permute (L:=L) σ).quasiMeasurePreserving.tendsto_ae.eventually (pull_ae N L J f)
  have hb := (config_preserving N L J).quasiMeasurePreserving.tendsto_ae.eventually (Measure.ae_smul_measure (hf σ) (ENNReal.ofReal (jacobian N L J)))
  filter_upwards [hσ,hb,pull_ae N L J f] with X hX hB hY
  change (pull N L J f) (fun i ↦ X (σ i))=amplitude N L J • f (config N L J (fun i ↦ X (σ i))) at hX
  rw [hX,hY]
  exact congrArg (fun z : ℂ ↦ amplitude N L J • z) hB

end HardSphere.Rescaling
end
end

end OAI
