import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Sequential compactness of finite measures

Normalization converts uniform tail estimates and a positive mass lower bound into
tightness of probability measures. A further subsequence of the masses recovers a
finite-measure limit while preserving the uniform mass bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal

theorem finiteMeasure_normalize_set_bound {d : ℕ} (μ : FiniteMeasure (Ambient d))
    (a b : ℝ) (ha : 0 < a) (hm : a ≤ (μ.mass : ℝ))
    (s : Set (Ambient d)) (hs : (μ s : ℝ) ≤ b) : (μ.normalize s : ℝ) ≤ b / a := by
  have heq : (μ s : ℝ) = (μ.mass : ℝ) * (μ.normalize s : ℝ) := by
    exact_mod_cast μ.self_eq_mass_mul_normalize s
  apply (le_div_iff₀ ha).mpr
  calc
    (μ.normalize s : ℝ) * a ≤ (μ.normalize s : ℝ) * (μ.mass : ℝ) :=
      mul_le_mul_of_nonneg_left hm (μ.normalize s).coe_nonneg
    _ = (μ s : ℝ) := by linarith only [heq]
    _ ≤ b := hs

theorem exists_normalized_measure_subsequence {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hm : ∀ j, a ≤ ((μ j).mass : ℝ))
    (ht : ∀ j R, 0 < R → ((μ j) (closedBall (0 : Ambient d) R)ᶜ : ℝ) ≤ B / R) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ P : ProbabilityMeasure (Ambient d),
      Tendsto (fun j => (μ (ρ j)).normalize) atTop (𝓝 P) := by
  let u : ℕ → ℝ≥0 := fun k => Real.toNNReal (B / a) * (1 / 2) ^ k
  let K : ℕ → Set (Ambient d) := fun k => closedBall 0 ((2 : ℝ) ^ k)
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa only [u, mul_zero] using!
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0) < 1)).const_mul
        (Real.toNNReal (B / a))
  have hc : IsCompact {P : ProbabilityMeasure (Ambient d) | ∀ k, P (K k)ᶜ ≤ u k} :=
    isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le hu
      (fun k => isCompact_closedBall 0 _) (Or.inl inferInstance)
  have hin : ∀ j, (μ j).normalize ∈ {P : ProbabilityMeasure (Ambient d) | ∀ k, P (K k)ᶜ ≤ u k} := by
    intro j k
    have hreal : ((μ j).normalize (K k)ᶜ : ℝ) ≤ (u k : ℝ) := by
      calc
        _ ≤ (B / (2 : ℝ) ^ k) / a := finiteMeasure_normalize_set_bound
          (μ j) a _ ha (hm j) (K k)ᶜ (ht j _ (by positivity))
        _ = (u k : ℝ) := by
          simp only [u, NNReal.coe_mul, Real.coe_toNNReal _ (div_nonneg hB ha.le), NNReal.coe_pow, NNReal.coe_div,
            NNReal.coe_one, NNReal.coe_ofNat, div_pow, one_pow]
          ring
    exact_mod_cast hreal
  obtain ⟨P, _hP, ρ, hρ, hlim⟩ := hc.tendsto_subseq hin
  exact ⟨ρ, hρ, P, hlim⟩

theorem exists_finite_measure_subsequence {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (a A B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hm : ∀ j, a ≤ ((μ j).mass : ℝ) ∧ ((μ j).mass : ℝ) ≤ A)
    (ht : ∀ j R, 0 < R → ((μ j) (closedBall (0 : Ambient d) R)ᶜ : ℝ) ≤ B / R) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : FiniteMeasure (Ambient d),
      Tendsto (fun j => μ (ρ j)) atTop (𝓝 ν) ∧ a ≤ (ν.mass : ℝ) ∧ (ν.mass : ℝ) ≤ A := by
  obtain ⟨ρ, hρ, P, hP⟩ := exists_normalized_measure_subsequence μ a B ha hB
    (fun j => (hm j).1) ht
  have hbounded : ∀ j, ((μ (ρ j)).mass : ℝ) ∈ Icc a A := fun j => hm (ρ j)
  obtain ⟨m, hmI, σ, hσ, hmass⟩ := isCompact_Icc.tendsto_subseq hbounded
  let m' : ℝ≥0 := ⟨m, ha.le.trans hmI.1⟩
  have hmass' : Tendsto (fun j => (μ (ρ (σ j))).mass) atTop (𝓝 m') :=
    NNReal.tendsto_coe.mp hmass
  have hP' : Tendsto (fun j => (μ (ρ (σ j))).normalize.toFiniteMeasure) atTop
      (𝓝 P.toFiniteMeasure) :=
    (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto P).comp
      (hP.comp hσ.tendsto_atTop)
  have hmasslim : (m' • P.toFiniteMeasure).mass = m' := by
    change (m' • P.toFiniteMeasure) univ = m'
    rw [FiniteMeasure.smul_apply]
    change m' * P.toFiniteMeasure.mass = m'
    rw [ProbabilityMeasure.mass_toFiniteMeasure, mul_one]
  refine ⟨ρ ∘ σ, hρ.comp hσ, m' • P.toFiniteMeasure, ?_, ?_, ?_⟩
  · have h := hmass'.smul hP'
    simpa only [← FiniteMeasure.self_eq_mass_smul_normalize, comp_apply] using! h
  · rw [hmasslim]
    exact hmI.1
  · rw [hmasslim]
    exact hmI.2

end

end RieszRectifiability

end OAI
