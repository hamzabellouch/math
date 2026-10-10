import OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma normalizedSlot_character (η ν : Character) (m A z : O)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t D : ℝ) :
    normalizedSlot η m A z S (fun P=>idealCoeff ν P*β P) t D=
      normalizedSlot (η.product ν) m A z S β t D := by
  unfold normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  rw [idealCoeff_product]
  ring

lemma product_row_presentation (η χ ν : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n) :
    ∀n,elementCoeff (χ.product ν) n=rowTwist (elementHom (η.product ν)) m 1 (A*z) n := by
  intro n
  rw [elementCoeff_product,hrow]
  change (elementCoeff η n*((idealRowHom (m^6*1^4*(A*z))).toMonoidHom.comp principalIdealHom.toMonoidHom) n)*elementCoeff ν n=
    elementCoeff (η.product ν) n*((idealRowHom (m^6*1^4*(A*z))).toMonoidHom.comp principalIdealHom.toMonoidHom) n
  rw [elementCoeff_product]
  ring

theorem relative_normalizedSlot_eq_ray (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ ν : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ→ℂ) (b D σ t v : ℝ) (hD : 0<D) :
    normalizedSlot η m A z (primePool M H b D)
      (fun P=>idealCoeff ν P*HeckePrimeAnnular.annularWeight W D σ v P) t D=
      (D:ℂ)^(Complex.I*t)*HeckePrimeRay.rayPrimePolynomial M H (χ.product ν) W b D σ (t+v) := by
  rw [normalizedSlot_character]
  exact CenteredMomentPrimeSlotShift.normalizedSlot_eq_ray M H (η.product ν) (χ.product ν)
    m A z (product_row_presentation η χ ν m A z hrow) W b D σ t v hD

theorem physicalSlot_eq_relativeRay (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (m A u : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*u) n)
    (W : ℝ→ℂ) (b D t : ℝ) (z : ℂ) (hD : 0<D) :
    normalizedSlot η m A u (primePool M H b D) (physicalSlotCoefficient η W D z) t D=
      (D:ℂ)^(Complex.I*t)*HeckePrimeRay.rayPrimePolynomial M H (χ.product η.inverse)
        (fun y=>conj (W y)) b D (1-z.re) (t-z.im) := by
  have he : normalizedSlot η m A u (primePool M H b D) (physicalSlotCoefficient η W D z) t D=
      normalizedSlot η m A u (primePool M H b D)
        (fun P=>idealCoeff η.inverse P*HeckePrimeAnnular.annularWeight (fun y=>conj (W y)) D (1-z.re) (-z.im) P) t D := by
    unfold normalizedSlot rowSlot
    congr 1
    apply Finset.sum_congr rfl
    intro P hP
    rw [physicalSlotCoefficient_annular η W D z P (Finset.mem_filter.mp hP).2.1.ne_zero hD]
  rw [he]
  exact relative_normalizedSlot_eq_ray M H η χ η.inverse m A u hrow
    (fun y=>conj (W y)) b D (1-z.re) t (-z.im) hD

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
