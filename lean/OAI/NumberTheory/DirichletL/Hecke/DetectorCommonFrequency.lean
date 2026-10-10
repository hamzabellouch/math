import OAI.NumberTheory.DirichletL.Hecke.DetectorFrequencyTail
import OAI.NumberTheory.DirichletL.Hecke.DetectorLower

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
namespace SevenEighths.HeckeDetectorFrequency
open HeckeFamily HeckeDetectorProfiles HeckeDetectorFourier HeckeDetectorLower
open HeckeDetectorCoefficientBounds HeckeDetectorFinite HeckeDetectorPartition
local notation "O" => HeckeFamily.O

def phaseProduct (χ : Character) (D U : ℝ) (s : ℂ) (j k : ℕ) (t : ℝ) : ℂ :=
  phasePolynomial (expandedSet U)
    (inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) D ((2 : ℝ)^j) s)
    (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^j)) t *
  phasePolynomial (expandedSet U)
    (plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) ((2 : ℝ)^k) s)
    (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^k)) t

theorem exists_common_frequency_witness (R θ τ : ℝ) (hR : 0 ≤ R)
    (hθ : 0 ≤ θ) (hθ' : θ < 3/4) (hτ : 0 < τ) :
    ∃ C U₀ : ℝ, 0 < C ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ χ : Character, χ.residue ≠ 1 → ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ∃ j ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
          ∃ t : ℝ, ‖t‖ ≤ U^τ ∧
            1 ≤ C*(Real.logb 2 U)^2*‖phaseProduct χ D U ρ j k t‖ ∧
            (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
            (2 : ℝ)^j*(2 : ℝ)^k < 8*U^21 := by
  obtain ⟨Ω,hΩc,hΩ,hwindow,hΩone⟩ := exists_product_log_cutoff
  obtain ⟨n,hn⟩ := exists_frequency_tail_order τ hτ
  have hL : 0 ≤ 2*Real.log 2+1 := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  obtain ⟨C₀,Cn,hC₀,hCn,hfreq⟩ := dyadic_frequency_bound Ω hΩc hΩ
    (2*Real.log 2+1) hL hwindow hΩone n
  obtain ⟨UF,hUF⟩ := hn Cn
  obtain ⟨UL,hUL⟩ := exists_dyadic_zero_witness R θ hR hθ hθ'
  refine ⟨2500*C₀,max 2 (max UF UL),by positivity,?_⟩
  intro U hU χ hχ D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hU1 : 1 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  obtain ⟨j,hj,k,hk,hblock,hsupport⟩ :=
    hUL U ((le_max_right UF UL).trans ((le_max_right 2 _).trans hU))
      χ hχ cutoff cutoff cutoff_norm_le cutoff_norm_le cutoff_one cutoff_zero cutoff_one cutoff_zero
      D hD hDU hQ ρ hρ hzero hheight
  obtain ⟨t,ht,hb⟩ := hfreq U D (U^τ) hU1 (by linarith) (by positivity) χ ρ (by linarith) j k
  have htail := hUF U ((le_max_left UF UL).trans ((le_max_right 2 _).trans hU)) hU1
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 625*(Real.logb 2 U)^2 by positivity)
  refine ⟨j,hj,k,hk,t,ht,?_,hsupport⟩
  change ‖dyadicBlock χ cutoff cutoff D (U^20) (U^21) ρ j k‖ ≤
    (67108864*U^42)*Cn/(U^τ)^n+C₀*‖phaseProduct χ D U ρ j k t‖ at hb
  change (625*(Real.logb 2 U)^2)*‖dyadicBlock χ cutoff cutoff D (U^20) (U^21) ρ j k‖ ≤
    (625*(Real.logb 2 U)^2)*((67108864*U^42)*Cn/(U^τ)^n+C₀*‖phaseProduct χ D U ρ j k t‖) at hb'
  nlinarith

end SevenEighths.HeckeDetectorFrequency

end

end OAI
