import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalCoupling

namespace OAI

/-! The physical coordinate change with the acceleration sources required
by the differentiated outgoing equation. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralPhysicalPair_source_hasDerivAt (μ lam η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ → ℂ) (Y : ℝ → E₄) (r : ℝ) (hr : 0 < r) (F G : ℂ)
    (hscale : (Complex.exp (μ*(Real.log r : ℂ))*
      star (Complex.exp (μ*(Real.log r : ℂ))))^m=1/(r : ℂ)^2)
    (hY : HasDerivAt Y (circularLeadingField (Real.log r) (Y (Real.log r))+
      circularBoundedField (μ-2*lam) (star μ-2*lam) η m (q (Real.log r))
        (Y (Real.log r)) + ((0, F), (0, G))) (Real.log r)) :
    HasDerivAt (spectralPhysicalPair (μ-2*lam) (star μ-2*lam) Y)
      (spectralPhysicalCircularField (μ-2*lam) (star μ-2*lam) η m
        (Complex.exp (μ*(Real.log r : ℂ))*q (Real.log r)) r
        (spectralPhysicalPair (μ-2*lam) (star μ-2*lam) Y r) +
        ((0, Complex.exp ((μ-2*lam)*(Real.log r : ℂ))/(r : ℂ)^2*F),
         (0, Complex.exp ((star μ-2*lam)*(Real.log r : ℂ))/(r : ℂ)^2*G))) r := by
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
    spectralCrossCoefficient m (q (Real.log r))*(Y (Real.log r)).2.1+F
  let Fm := star (spectralDiagonalCoefficient m (q (Real.log r)))*(Y (Real.log r)).2.1+
    star (spectralCrossCoefficient m (q (Real.log r)))*(Y (Real.log r)).1.1+G
  have hdP : HasDerivAt (fun t => (Y t).1)
      ((Y (Real.log r)).1.2,-(2*(μ-2*lam)+10)*(Y (Real.log r)).1.2-
      ((μ-2*lam)*((μ-2*lam)+10)-η)*(Y (Real.log r)).1.1-
      (1 : ℂ)*Complex.I*(Real.exp (2*Real.log r)/2 : ℝ)*(Y (Real.log r)).1.2+Fp)
      (Real.log r) := by
    apply ((ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt
      (Real.log r) hY).congr_deriv
    rw [ContinuousLinearMap.coe_fst']
    apply Prod.ext
    · simp [circularLeadingField, circularBoundedField]
    · dsimp only [Fp, circularLeadingField, circularBoundedField, Prod.fst_add, Prod.snd_add]
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
    · simp [circularLeadingField, circularBoundedField]
    · dsimp only [Fm, circularLeadingField, circularBoundedField, Prod.fst_add, Prod.snd_add]
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
  · simp only [Prod.fst_add, add_zero]
    rfl
  · dsimp only [spectralPhysicalPair,spectralPhysicalCircularField,spectralPhysicalJet,Fp,Prod.fst_add,Prod.snd_add]
    rw [hp,hmexp]
    dsimp only [A] at hsp ⊢
    simp only [one_mul]
    linear_combination -hsp
  · simp only [Prod.fst_add, Prod.snd_add, add_zero]
    rfl
  · dsimp only [spectralPhysicalPair,spectralPhysicalCircularField,spectralPhysicalJet,Fm,Prod.fst_add,Prod.snd_add]
    rw [hp,hmexp]
    dsimp only [A] at hsm ⊢
    linear_combination -hsm


end DefocusingNLS

end OAI
