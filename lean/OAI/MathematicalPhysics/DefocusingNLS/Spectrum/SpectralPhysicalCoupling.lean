import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalJet
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoefficientScaling
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularField

namespace OAI

/-! Exact recovery of the coupled physical spectral equation from its normalized system. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralPhysicalPair (νp νm : ℂ) (Y : ℝ → E₄) (r : ℝ) : E₄ :=
  (spectralPhysicalJet νp (fun t => (Y t).1) r,
   spectralPhysicalJet νm (fun t => (Y t).2) r)

noncomputable def spectralPhysicalCircularField (νp νm η : ℂ) (m : ℕ)
    (Q : ℂ) (r : ℝ) (V : E₄) : E₄ :=
  ((V.1.2,-(11/(r : ℂ)+Complex.I*(r : ℂ)/2)*V.1.2-
      (-Complex.I*νp/2-η/(r : ℂ)^2)*V.1.1+
      spectralDiagonalCoefficient m Q*V.1.1+spectralCrossCoefficient m Q*V.2.1),
   (V.2.2,-(11/(r : ℂ)-Complex.I*(r : ℂ)/2)*V.2.2-
      (Complex.I*νm/2-η/(r : ℂ)^2)*V.2.1+
      star (spectralDiagonalCoefficient m Q)*V.2.1+
      star (spectralCrossCoefficient m Q)*V.1.1))

theorem spectralPhysicalPair_hasDerivAt (μ lam η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ → ℂ) (Y : ℝ → E₄) (r : ℝ) (hr : 0 < r)
    (hscale : (Complex.exp (μ*(Real.log r : ℂ))*
      star (Complex.exp (μ*(Real.log r : ℂ))))^m=1/(r : ℂ)^2)
    (hY : HasDerivAt Y (circularLeadingField (Real.log r) (Y (Real.log r))+
      circularBoundedField (μ-2*lam) (star μ-2*lam) η m (q (Real.log r))
        (Y (Real.log r))) (Real.log r)) :
    HasDerivAt (spectralPhysicalPair (μ-2*lam) (star μ-2*lam) Y)
      (spectralPhysicalCircularField (μ-2*lam) (star μ-2*lam) η m
        (Complex.exp (μ*(Real.log r : ℂ))*q (Real.log r)) r
        (spectralPhysicalPair (μ-2*lam) (star μ-2*lam) Y r)) r := by
  let A := Complex.exp (μ*(Real.log r : ℂ))
  let L := Complex.exp ((-2*lam)*(Real.log r : ℂ))
  have hp : Complex.exp ((μ-2*lam)*(Real.log r : ℂ))=A*L := by
    dsimp only [A,L]
    rw [← Complex.exp_add]
    congr 1
    ring
  have hmexp : Complex.exp ((star μ-2*lam)*(Real.log r : ℂ))=star A*L := by
    dsimp only [A,L]
    rw [Complex.star_def,← Complex.exp_conj,← Complex.exp_add]
    congr 1
    simp only [map_mul,Complex.conj_ofReal]
    ring
  let Fp := spectralDiagonalCoefficient m (q (Real.log r))*(Y (Real.log r)).1.1+
    spectralCrossCoefficient m (q (Real.log r))*(Y (Real.log r)).2.1
  let Fm := star (spectralDiagonalCoefficient m (q (Real.log r)))*(Y (Real.log r)).2.1+
    star (spectralCrossCoefficient m (q (Real.log r)))*(Y (Real.log r)).1.1
  have hdP : HasDerivAt (fun t => (Y t).1)
      ((Y (Real.log r)).1.2,-(2*(μ-2*lam)+10)*(Y (Real.log r)).1.2-
      ((μ-2*lam)*((μ-2*lam)+10)-η)*(Y (Real.log r)).1.1-
      (1 : ℂ)*Complex.I*(Real.exp (2*Real.log r)/2 : ℝ)*(Y (Real.log r)).1.2+Fp)
      (Real.log r) := by
    apply ((ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt
      (Real.log r) hY).congr_deriv
    rw [ContinuousLinearMap.coe_fst']
    apply Prod.ext
    · exact zero_add _
    · change -Complex.I*(Real.exp (2*Real.log r)/2 : ℝ)*(Y (Real.log r)).1.2+
        (-(2*(μ-2*lam)+10)*(Y (Real.log r)).1.2-
          ((μ-2*lam)*((μ-2*lam)+10)-η)*(Y (Real.log r)).1.1+
          spectralDiagonalCoefficient m (q (Real.log r))*(Y (Real.log r)).1.1+
          spectralCrossCoefficient m (q (Real.log r))*(Y (Real.log r)).2.1)=_
      dsimp only [Fp]
      ring
  have hdM : HasDerivAt (fun t => (Y t).2)
      ((Y (Real.log r)).2.2,-(2*(star μ-2*lam)+10)*(Y (Real.log r)).2.2-
      ((star μ-2*lam)*((star μ-2*lam)+10)-η)*(Y (Real.log r)).2.1-
      (-1 : ℂ)*Complex.I*(Real.exp (2*Real.log r)/2 : ℝ)*(Y (Real.log r)).2.2+Fm)
      (Real.log r) := by
    apply ((ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt
      (Real.log r) hY).congr_deriv
    rw [ContinuousLinearMap.coe_snd']
    apply Prod.ext
    · exact zero_add _
    · change Complex.I*(Real.exp (2*Real.log r)/2 : ℝ)*(Y (Real.log r)).2.2+
        (-(2*(star μ-2*lam)+10)*(Y (Real.log r)).2.2-
          ((star μ-2*lam)*((star μ-2*lam)+10)-η)*(Y (Real.log r)).2.1+
          star (spectralDiagonalCoefficient m (q (Real.log r)))*(Y (Real.log r)).2.1+
          star (spectralCrossCoefficient m (q (Real.log r)))*(Y (Real.log r)).1.1)=_
      dsimp only [Fm]
      ring
  have hsp := spectralCircularCoefficient_scale m hm A L (q (Real.log r))
    (Y (Real.log r)).1.1 (Y (Real.log r)).2.1 (1/(r : ℂ)^2) hscale
  have hsm := congrArg star (spectralCircularCoefficient_scale m hm A (star L)
    (q (Real.log r)) (star (Y (Real.log r)).2.1) (star (Y (Real.log r)).1.1)
    (1/(r : ℂ)^2) hscale)
  have hrs : star (1/(r : ℂ)^2)=1/(r : ℂ)^2 := by simp
  simp only [star_add,star_mul,star_star,hrs] at hsm
  apply ((spectralPhysicalJet_hasDerivAt 1 (μ-2*lam) η _ r hr Fp hdP).prodMk
    (spectralPhysicalJet_hasDerivAt (-1) (star μ-2*lam) η _ r hr Fm hdM)).congr_deriv
  apply Prod.ext <;> apply Prod.ext
  · rfl
  · dsimp only [spectralPhysicalPair,spectralPhysicalCircularField,spectralPhysicalJet,Fp]
    rw [hp,hmexp]
    dsimp only [A] at hsp ⊢
    simp only [one_mul]
    linear_combination -hsp
  · rfl
  · dsimp only [spectralPhysicalPair,spectralPhysicalCircularField,spectralPhysicalJet,Fm]
    rw [hp,hmexp]
    dsimp only [A] at hsm ⊢
    linear_combination -hsm

end DefocusingNLS

end OAI
