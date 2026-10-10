import OAI.NumberTheory.DirichletL.Hecke.DetectorCommonFrequency
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicCutoff

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorNormalized
open HeckeFamily HeckeDyadic HeckeDetectorFourier HeckeDetectorProfiles
open HeckeDetectorDyadicBridge HeckeDetectorDyadicProfiles HeckeDetectorFrequency

lemma plainCoefficient_positive (χ : Character) (D : ℝ) (hD : 0<D) (s : ℂ) :
    plainCoefficient χ positiveAnnular D s=
      plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) D s := by
  funext J
  unfold plainCoefficient
  rw [positiveAnnular_eq _ (div_nonneg (Nat.cast_nonneg _) hD.le)]

lemma inverseCoefficient_positive (χ : Character) (Dstar D : ℝ) (hD : 0<D) (s : ℂ) :
    inverseCoefficient χ cutoff positiveAnnular Dstar D s=
      inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar D s := by
  funext J
  unfold inverseCoefficient
  rw [positiveAnnular_eq _ (div_nonneg (Nat.cast_nonneg _) hD.le)]

theorem phaseProduct_norm (χ : Character) (Dstar U : ℝ) (s : ℂ) (j k : ℕ) (t : ℝ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U^21) :
    ‖phaseProduct χ Dstar U s j k t‖ =
      ((2 : ℝ)^j)^(1/2-s.re)*((2 : ℝ)^k)^(1/2-s.re)*
        (‖polynomial χ true (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((2 : ℝ)^j))
            ((2 : ℝ)^j) s.re (2*Real.pi*t-s.im)‖ *
         ‖polynomial χ false positiveAnnular ((2 : ℝ)^k) s.re (2*Real.pi*t-s.im)‖) := by
  obtain ⟨hj,hk⟩ := scales_le_eight_terminal (U^21) j k hprod
  have hDj : 0<(2 : ℝ)^j := by positivity
  have hNk : 0<(2 : ℝ)^k := by positivity
  unfold phaseProduct
  rw [norm_mul, ← inverseCoefficient_positive χ Dstar ((2 : ℝ)^j) hDj s,
    ← plainCoefficient_positive χ ((2 : ℝ)^k) hNk s]
  exact pair_phase_norm χ cutoff positiveAnnular positiveAnnular Dstar ((2 : ℝ)^j) ((2 : ℝ)^k)
    hDj hNk s t (fourierSet (U^21)) (fourierSet (U^21))
    (fourierSet_nonzero (U^21)) (fourierSet_nonzero (U^21))
    (inverse_annular_covered (U^21) ((2 : ℝ)^j) Dstar hDj hj cutoff positiveAnnular positiveAnnular_zero)
    (annular_covered (U^21) ((2 : ℝ)^k) hNk hk positiveAnnular positiveAnnular_zero)

theorem exists_normalized_product (R θ τ : ℝ) (hR : 0≤R)
    (hθ : 0≤θ) (hθ' : θ<3/4) (hτ : 0<τ) :
    ∃ C U₀ : ℝ, 0<C ∧ ∀ U : ℝ, U₀≤U →
      ∀ χ : Character, χ.residue≠1 → ∀ Dstar : ℝ, 2≤Dstar → Dstar≤U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ)≤R*U → ∀ ρ : ℂ,
      (51/100 : ℝ)≤ρ.re → LFunction χ ρ=0 → |ρ.im|≤U^θ →
      ∃ j∈Finset.range (HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k∈Finset.range (HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1),
          ∃ t : ℝ, ‖t‖≤U^τ ∧
            1≤C*(Real.logb 2 U)^2*((2 : ℝ)^j)^(1/2-ρ.re)*((2 : ℝ)^k)^(1/2-ρ.re)*
              (‖polynomial χ true (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((2 : ℝ)^j))
                  ((2 : ℝ)^j) ρ.re (2*Real.pi*t-ρ.im)‖ *
               ‖polynomial χ false positiveAnnular ((2 : ℝ)^k) ρ.re (2*Real.pi*t-ρ.im)‖) ∧
            (2 : ℝ)^j<4*Dstar ∧ Dstar/8<(2 : ℝ)^j*(2 : ℝ)^k ∧
            (2 : ℝ)^j*(2 : ℝ)^k<8*U^21 := by
  obtain ⟨C,U₀,hC,hbound⟩ := exists_common_frequency_witness R θ τ hR hθ hθ' hτ
  refine ⟨C,U₀,hC,?_⟩
  intro U hU χ hχ Dstar hD hDU hQ ρ hρ hzero hheight
  obtain ⟨j,hj,k,hk,t,ht,hb,hd,hn,hprod⟩ := hbound U hU χ hχ Dstar hD hDU hQ ρ hρ hzero hheight
  refine ⟨j,hj,k,hk,t,ht,?_,hd,hn,hprod⟩
  rw [phaseProduct_norm χ Dstar U ρ j k t hprod] at hb
  convert hb using 1; ring

end SevenEighths.HeckeDetectorNormalized

end

end OAI
