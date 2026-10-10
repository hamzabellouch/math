import Mathlib
import OAI.Probability.SKRatio.Matrices.UnitInterval

namespace OAI

section
section
noncomputable section
namespace SKRatioGaussian.PathBridge
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal Topology

def pathEnergy (n : ℕ) (f : Fin n→UnitPath) : ℝ := ∑ i,‖f i‖^2

lemma energy_exponential_prod (n : ℕ) (a : ℝ) (f : Fin n→UnitPath) :
    exp (a*pathEnergy n f)=∏ i,exp (a*‖f i‖^2) := by
  rw [pathEnergy,Finset.mul_sum,exp_sum]

lemma pathEnergy_exponential_integrable (μ : Measure UnitPath) [IsProbabilityMeasure μ]
    (a : ℝ) (hi : Integrable (fun f : UnitPath=>exp (a*‖f‖^2)) μ) (n : ℕ) :
    Integrable (fun f=>exp (a*pathEnergy n f)) (Measure.pi (fun _ : Fin n=>μ)) := by
  simp_rw [energy_exponential_prod]
  exact Integrable.fintype_prod (fun _=>hi)

lemma pathEnergy_exponential_integral (μ : Measure UnitPath) [IsProbabilityMeasure μ]
    (a : ℝ) (n : ℕ) :
    (∫ f,exp (a*pathEnergy n f) ∂Measure.pi (fun _ : Fin n=>μ))=
      (∫ f : UnitPath,exp (a*‖f‖^2) ∂μ)^n := by
  simp_rw [energy_exponential_prod]
  simpa using integral_fintype_prod_eq_pow (ι:=Fin n) (μ:=μ) (fun f : UnitPath=>exp (a*‖f‖^2))

theorem pathEnergy_dimension_tail (μ : Measure UnitPath) [IsProbabilityMeasure μ]
    (hG : IsGaussianProcess (fun t : UnitInterval=>fun f : UnitPath=>f t) μ)
    (h0 : ∀ t : UnitInterval, ∫ f : UnitPath,f t ∂μ=0) :
    ∃ H : ℝ, 0<H ∧ ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n=>μ)).real {f | H*(n:ℝ) ≤ pathEnergy n f} ≤ exp (-(n:ℝ)) := by
  obtain ⟨a,ha,hi⟩ := centered_gaussian_path_fernique μ hG h0
  let M := ∫ f : UnitPath,exp (a*‖f‖^2) ∂μ
  have hM : 1≤M := by
    calc
      1 = ∫ _ : UnitPath,(1:ℝ) ∂μ := by simp
      _ ≤ M := integral_mono (integrable_const _) hi (fun f=>by
        exact one_le_exp_iff.mpr (mul_nonneg ha.le (sq_nonneg _)))
  have hMp : 0<M := lt_of_lt_of_le zero_lt_one hM
  let H := (log M+1)/a
  have hH : 0<H := div_pos (by linarith [log_nonneg hM]) ha
  refine ⟨H,hH,fun n=>?_⟩
  calc
    _ ≤ exp (-a*(H*(n:ℝ)))*mgf (pathEnergy n) (Measure.pi (fun _ : Fin n=>μ)) a :=
      measure_ge_le_exp_mul_mgf _ ha.le (pathEnergy_exponential_integrable μ a hi n)
    _ = exp (-(n:ℝ)) := by
      rw [mgf,pathEnergy_exponential_integral]
      change exp (-a*(H*(n:ℝ)))*M^n=_
      rw [← exp_log hMp,← exp_nat_mul,← exp_add]
      congr 1
      dsimp [H]
      field_simp
      ring

theorem scaledPath_dimension_tail (μ : Measure UnitPath) [IsProbabilityMeasure μ]
    (hG : IsGaussianProcess (fun t : UnitInterval=>fun f : UnitPath=>f t) μ)
    (h0 : ∀ t : UnitInterval, ∫ f : UnitPath,f t ∂μ=0) {κ : ℝ} (hκ : 0<κ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n=>μ)).real
        {f | κ^2*(n:ℝ) ≤ δ*pathEnergy n f} ≤ exp (-(n:ℝ)) := by
  obtain ⟨H,hH,ht⟩ := pathEnergy_dimension_tail μ hG h0
  refine ⟨κ^2/H,div_pos (sq_pos_of_pos hκ) hH,fun n=>?_⟩
  convert ht n using 2
  ext f
  simp only [Set.mem_ofPred_eq]
  rw [div_mul_eq_mul_div,le_div_iff₀ hH]
  constructor <;> intro h
  · nlinarith [sq_pos_of_pos hκ]
  · nlinarith [sq_pos_of_pos hκ]
end SKRatioGaussian.PathBridge

end
end

section

noncomputable section

end
end
end

end OAI
