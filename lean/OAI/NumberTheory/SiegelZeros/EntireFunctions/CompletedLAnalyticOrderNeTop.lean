import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.RealLogDerivConductorCompletedLDivisorTsum
import OAI.NumberTheory.SiegelZeros.Structure.CharacterEstimates

namespace OAI

namespace SiegelZeros
open scoped _root_.SiegelZeros

section
section

open scoped BigOperators Topology

section

open Filter Set MeasureTheory
open scoped Topology

namespace WeightedTorusJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.SiegelZeros.Real Set MeasureTheory

end WeightedTorusJets

namespace WeightedTorusJets

open Filter Set MeasureTheory _root_.SiegelZeros.Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end WeightedTorusJets

open Filter Set Asymptotics

namespace WeightedTorusJets

end WeightedTorusJets

namespace WeightedTorusJets

end WeightedTorusJets

namespace WeightedTorusJets

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.SiegelZeros.Complex DirichletCharacter

variable {q : ℕ} [NeZero q]

theorem completedL_analyticOrderAt_ne_top (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (s : ℂ) : analyticOrderAt (completedLFunction χ) s ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
    (differentiable_completedLFunction hχ).analyticAt]
  intro hzero
  have hnonzero := completedL_ne_zero_of_one_le_re χ hχ (s := 1) (by simp)
  exact hnonzero (congrFun hzero 1)

theorem completedL_analyticOrderNatAt_pos_iff (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (s : ℂ) :
    0 < analyticOrderNatAt (completedLFunction χ) s ↔ completedLFunction χ s = 0 := by
  rw [Nat.pos_iff_ne_zero, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero,
    not_or, and_iff_left (completedL_analyticOrderAt_ne_top χ hχ s)]
  exact ((differentiable_completedLFunction hχ).analyticAt s).analyticOrderAt_ne_zero

theorem finite_completedL_zeros_on_compact (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {K : Set ℂ} (hK : IsCompact K) :
    {s ∈ K | completedLFunction χ s = 0}.Finite := by
  have ha : AnalyticOnNhd ℂ (completedLFunction χ) Set.univ :=
    fun z _ => (differentiable_completedLFunction hχ).analyticAt z
  have hz := ha.preimage_zero_mem_codiscrete
    (completedL_ne_zero_of_one_le_re χ hχ (s := 1) (by simp))
  have hk := hK.finite_sdiff_of_mem_codiscreteWithin
    ((Filter.codiscreteWithin_mono (Set.subset_univ K)) hz)
  convert hk using 1
  ext s
  simp

end WeightedTorusJets

namespace WeightedTorusJets

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.SiegelZeros.Complex.Hadamard

variable {q : ℕ} [NeZero q]

end WeightedTorusJets

namespace WeightedTorusJets

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.SiegelZeros.Complex DirichletCharacter

section RealPart

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

local notation "ZeroIndices" => Σ z : ℂ, Fin (analyticOrderNatAt (conductorCompletedL χ) z)

end RealPart

end WeightedTorusJets

namespace RealCharacterAnalysis

open _root_.SiegelZeros.Complex _root_.SiegelZeros.Complex.Hadamard

theorem divisorCanonicalProduct_eq_tprod_analytic {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (m : ℕ) (s : ℂ) :
    divisorCanonicalProduct m f Set.univ s =
      ∏' p : Σ z : ℂ, Fin (analyticOrderNatAt f z), weierstrassFactor m (s / p.1) := by
  simpa only [divisorCanonicalProduct, divisorIndexEquivAnalytic_val] using
    (divisorIndexEquivAnalytic hf h0).tprod_eq (fun p => weierstrassFactor m (s / p.1))

end RealCharacterAnalysis
namespace WeightedTorusJets

open _root_.SiegelZeros.Complex DirichletCharacter _root_.SiegelZeros.Complex.Hadamard RealCharacterAnalysis

section

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

local notation "DivisorIndices" => divisorZeroIndex₀ (conductorCompletedL χ) Set.univ

end

end WeightedTorusJets

namespace WeightedTorusJets

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.SiegelZeros.Complex.Hadamard

end WeightedTorusJets
namespace WeightedTorusJets

open _root_.SiegelZeros.Complex DirichletCharacter _root_.SiegelZeros.Complex.Hadamard

end WeightedTorusJets

end
section

open Filter Set
open scoped Topology

namespace WeightedTorusJets

end WeightedTorusJets

end
section

open scoped Classical

namespace WeightedTorusJets

theorem gammaFactor_real_parity_argument {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℝ) :
    χ.gammaFactor (s : ℂ) =
      Complex.Gammaℝ ((s + (1 - (χ (-1)).re) / 2 : ℝ) : ℂ) := by
  rw [character_parity_parameter_real]
  by_cases h : χ.Even <;> simp [DirichletCharacter.gammaFactor, h]

end WeightedTorusJets

end
section
namespace WeightedTorusJets

end WeightedTorusJets
end
section

open Filter Set
open scoped Topology

namespace WeightedTorusJets

theorem exists_upper_bound_zeta_logDeriv_log :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      (-logDeriv riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ)).re ≤ Real.log X + C := by
  obtain ⟨C, hC, hbound⟩ := exists_upper_bound_zeta_logDeriv_re
  refine ⟨C, hC, ?_⟩
  intro X hX
  have hlog : 1 < Real.log X := (Real.lt_log_iff_exp_lt (by linarith)).mpr
    (Real.exp_one_lt_three.trans_le hX)
  have hpos : 0 < 1 / Real.log X := one_div_pos.mpr (by linarith)
  have hle : 1 / Real.log X ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlog.le
  simpa using hbound (1 + 1 / Real.log X) (by linarith) (by linarith)

end WeightedTorusJets
end
section
namespace WeightedTorusJets

end WeightedTorusJets
end
section

open scoped BigOperators

namespace WeightedTorusJets

open ArithmeticFunction DirichletCharacter

end WeightedTorusJets
end
section

namespace WeightedTorusJets

end WeightedTorusJets
end
section
namespace WeightedTorusJets

end WeightedTorusJets
end
section

open _root_.Complex _root_.SiegelZeros.Complex Filter
open scoped Topology ComplexConjugate

namespace RealCharacterAnalysis

theorem quadratic_prime_values {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (hp : p.Prime) (hpq : ¬ p ∣ q) :
    χ (p : ZMod q) = 1 ∨ χ (p : ZMod q) = -1 := by
  rcases hχ (p : ZMod q) with h | h
  · exact (hpq ((apply_prime_eq_zero_iff χ hp).mp h)).elim
  · exact h

theorem deriv_lFunction_conj {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    deriv (DirichletCharacter.LFunction χ⁻¹) (conj s) =
      conj (deriv (DirichletCharacter.LFunction χ) s) := by
  have heq : DirichletCharacter.LFunction χ⁻¹ =
      conj ∘ DirichletCharacter.LFunction χ ∘ conj := by
    funext z
    simpa using lFunction_conj χ hχ (conj z)
  rw [heq, deriv_conj_conj]
  simp

theorem deriv_lFunction_real {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hr : ∀ a : ZMod q, (χ a).im = 0) (s : ℝ) :
    (deriv (DirichletCharacter.LFunction χ) (s : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [← deriv_lFunction_conj χ hχ, Complex.conj_ofReal,
    ((real_values_iff_quadratic χ).mp hr).inv]

theorem logarithmic_derivative_real {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hr : ∀ a : ZMod q, (χ a).im = 0) (s : ℝ) :
    (deriv (DirichletCharacter.LFunction χ) (s : ℂ) /
      DirichletCharacter.LFunction χ (s : ℂ)).im = 0 := by
  simp [Complex.div_im, deriv_lFunction_real χ hχ hr, lFunction_real χ hχ hr]

theorem quadratic_nonprincipal_has_negative_value {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hr : χ.IsQuadratic) :
    ∃ a : (ZMod q)ˣ, χ a = -1 := by
  obtain ⟨a, ha⟩ := MulChar.ne_one_iff.mp hχ
  refine ⟨a, ?_⟩
  rcases hr a with h | h | h
  · exact ((MulChar.apply_ne_zero_iff.mpr a.isUnit) h).elim
  · exact (ha h).elim
  · exact h

theorem gammaR_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  have hp : (Real.pi : ℂ) ^ conj (-s / 2) = conj ((Real.pi : ℂ) ^ (-s / 2)) := by
    simpa using Complex.cpow_conj (Real.pi : ℂ) (-s / 2)
      (by simp [Complex.arg_ofReal_of_nonneg Real.pi_pos.le, Real.pi_ne_zero.symm])
  simpa only [Gammaℝ_def, map_mul, map_div₀, map_neg, map_ofNat] using congrArg₂ (fun a b : ℂ => a * b) hp
    (Complex.Gamma_conj (s / 2))

theorem gammaFactor_inv_conj {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    DirichletCharacter.gammaFactor χ⁻¹ (conj s) =
      conj (DirichletCharacter.gammaFactor χ s) := by
  have hpar : χ⁻¹.Even ↔ χ.Even := by
    rw [← MulChar.star_eq_inv]
    change conj (χ (-1)) = 1 ↔ χ (-1) = 1
    constructor
    · intro h
      apply (starRingEnd ℂ).injective
      simpa only [map_one] using h
    · intro h
      simp only [h, map_one]
  classical
  by_cases he : χ.Even
  · rw [DirichletCharacter.gammaFactor, DirichletCharacter.gammaFactor,
      ite_eq_left he, ite_eq_left (hpar.mpr he)]
    exact gammaR_conj s
  · rw [DirichletCharacter.gammaFactor, DirichletCharacter.gammaFactor,
      ite_eq_right he, ite_eq_right (fun h => he (hpar.mp h))]
    simpa only [map_add, map_one] using gammaR_conj (s + 1)

theorem completed_lFunction_conj {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.completedLFunction χ⁻¹ (conj s) =
      conj (DirichletCharacter.completedLFunction χ s) := by
  have hi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have hf := DirichletCharacter.differentiable_completedLFunction hi
  have hg : Differentiable ℂ
      (conj ∘ DirichletCharacter.completedLFunction χ ∘ conj) := by
    intro z
    simpa using
      (DirichletCharacter.differentiable_completedLFunction hχ (conj z)).conj_conj
  have heq : DirichletCharacter.completedLFunction χ⁻¹ =
      conj ∘ DirichletCharacter.completedLFunction χ ∘ conj := by
    apply (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
      (hg.differentiableOn.analyticOnNhd isOpen_univ)
    have hn : {z : ℂ | 0 < z.re} ∈ nhds (1 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn] with z hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have hgamma : DirichletCharacter.gammaFactor χ⁻¹ z ≠ 0 := by
      rcases χ⁻¹.even_or_odd with heven | hodd
      · rw [heven.gammaFactor_def]
        exact Gammaℝ_ne_zero_of_re_pos hz
      · rw [hodd.gammaFactor_def]
        apply Gammaℝ_ne_zero_of_re_pos
        simp only [add_re, one_re]
        linarith
    have h := lFunction_conj χ hχ (conj z)
    simp only [Complex.conj_conj] at h
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ z (.inl hz0),
      DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ (conj z)
        (.inl (by simpa using hz0)), map_div₀,
      ← gammaFactor_inv_conj, Complex.conj_conj] at h
    exact (div_left_inj' hgamma).mp h
  simpa using congrFun heq (conj s)

theorem completed_lFunction_real {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hr : ∀ a : ZMod q, (χ a).im = 0) (s : ℝ) :
    (DirichletCharacter.completedLFunction χ (s : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [← completed_lFunction_conj χ hχ, Complex.conj_ofReal,
    ((real_values_iff_quadratic χ).mp hr).inv]

theorem deriv_completed_lFunction_conj {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    deriv (DirichletCharacter.completedLFunction χ⁻¹) (conj s) =
      conj (deriv (DirichletCharacter.completedLFunction χ) s) := by
  have heq : DirichletCharacter.completedLFunction χ⁻¹ =
      conj ∘ DirichletCharacter.completedLFunction χ ∘ conj := by
    funext z
    simpa using completed_lFunction_conj χ hχ (conj z)
  rw [heq, deriv_conj_conj]
  simp

theorem deriv_completed_lFunction_real {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hr : ∀ a : ZMod q, (χ a).im = 0) (s : ℝ) :
    (deriv (DirichletCharacter.completedLFunction χ) (s : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [← deriv_completed_lFunction_conj χ hχ, Complex.conj_ofReal,
    ((real_values_iff_quadratic χ).mp hr).inv]

theorem logDeriv_completed_lFunction_real {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hr : ∀ a : ZMod q, (χ a).im = 0) (s : ℝ) :
    (logDeriv (DirichletCharacter.completedLFunction χ) (s : ℂ)).im = 0 := by
  simp [logDeriv, Complex.div_im, deriv_completed_lFunction_real χ hχ hr,
    completed_lFunction_real χ hχ hr]

end RealCharacterAnalysis
end

end
end

end SiegelZeros

end OAI
