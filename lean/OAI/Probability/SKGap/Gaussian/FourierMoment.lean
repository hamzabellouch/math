import Mathlib
import OAI.Probability.SKGap.Localization.EntryLM

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix
open MeasureTheory NormedSpace
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def fourierMoment (f : 𝓢(ℝ,ℂ)) (k : ℕ) : ℝ :=
  ∫ t : ℝ, ‖(𝓕 f) t‖*|t|^k

lemma fourierMoment_nonneg (f : 𝓢(ℝ,ℂ)) (k : ℕ) : 0 ≤ fourierMoment f k := by
  apply integral_nonneg
  intro t
  positivity

lemma fourierMoment_integrable (f : 𝓢(ℝ,ℂ)) (k : ℕ) :
    Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|^k) := by
  simpa only [Real.norm_eq_abs,mul_comm] using (𝓕 f).integrable_pow_mul volume k

lemma opNorm_rsmul (r : ℝ) (M : Matrix ι ι ℂ) : opNorm (r • M) = |r| * opNorm M := by
  change opNorm ((r:ℂ) • M) = _
  rw [opNorm_csmul,Complex.norm_real,Real.norm_eq_abs]

lemma schwartzMatrix_lipschitz (f : 𝓢(ℝ,ℂ)) (M N : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖schwartzMatrix f M-schwartzMatrix f N‖ ≤
      (2*Real.pi*fourierMoment f 1)*‖M-N‖ := by
  have hf₁ : Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|) := by
    simpa only [pow_one] using fourierMoment_integrable f 1
  have hh := kernelMatrix_lipschitz (𝓕 f).integrable hf₁
    ((2*Real.pi:ℝ) • M) ((2*Real.pi:ℝ) • N) (by simp [hM]) (by simp [hN])
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2*Real.pi:ℝ))] at hh
  exact hh.trans_eq (by simp only [fourierMoment,pow_one]; ring)

lemma schwartzMatrix_four_point (f : 𝓢(ℝ,ℂ)) (a b c d : Matrix ι ι ℂ)
    (ha : aᴴ = a) (hb : bᴴ = b) (hc : cᴴ = c) (hd : dᴴ = d) :
    ‖(schwartzMatrix f a-schwartzMatrix f b)-(schwartzMatrix f c-schwartzMatrix f d)‖ ≤
      (2*Real.pi*fourierMoment f 1)*‖(a-b)-(c-d)‖ +
      ((2*Real.pi)^2*fourierMoment f 2)*(opNorm (a-c)+opNorm (b-d))*‖c-d‖ := by
  have hf₁ : Integrable (fun t : ℝ => ‖(𝓕 f) t‖*|t|) := by
    simpa only [pow_one] using fourierMoment_integrable f 1
  have hh := kernelMatrix_four_point (𝓕 f).integrable hf₁ (fourierMoment_integrable f 2)
    ((2*Real.pi:ℝ) • a) ((2*Real.pi:ℝ) • b) ((2*Real.pi:ℝ) • c) ((2*Real.pi:ℝ) • d)
    (by simp [ha]) (by simp [hb]) (by simp [hc]) (by simp [hd])
  simp only [← smul_sub,norm_smul,opNorm_rsmul,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < (2*Real.pi:ℝ))] at hh
  exact hh.trans_eq (by simp only [fourierMoment,pow_one]; ring)

end SKGap.ComplexMatrix

end

end OAI
