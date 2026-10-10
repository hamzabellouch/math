import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspPrimeSupport

namespace OAI

/-! Removing an unramified prime cube preserves the exact arithmetic
support. Consequently cube scaling holds on every index, including the
zero extension of all three coefficient families. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCoordinates_primeCube_dvd {p n : Eisenstein} (hp : primaryPrime p)
    (R : CubicThetaCoordinates (n*p^3)) : p ∣ R.cubePart := by
  by_contra hd
  have hpu : IsCoprime p (R.unit:Eisenstein) := hp.2.coprime_iff_not_dvd.mpr
    (fun hv => hp.2.not_isUnit (isUnit_of_dvd_unit hv R.unit.isUnit))
  have hpl : IsCoprime p (lambdaE^R.order) := (primary_coprime_lambda hp.1).pow_right
  have hpd : IsCoprime p (R.cubePart^3) := (hp.2.coprime_iff_not_dvd.mpr hd).pow_right
  have hc : p^2 ∣ R.squarefreePart := by
    have heq : n*p^3=((R.unit:Eisenstein)*lambdaE^R.order*R.cubePart^3)*R.squarefreePart :=
      R.numerator_eq.trans (by ring)
    have he : p^2 ∣ ((R.unit:Eisenstein)*lambdaE^R.order*R.cubePart^3)*R.squarefreePart :=
      ((pow_dvd_pow p (by omega : 2 ≤ 3)).trans (dvd_mul_left (p^3) n)).trans (dvd_of_eq heq)
    exact ((hpu.mul_right hpl).mul_right hpd).pow_left.dvd_of_dvd_mul_left he
  exact hp.2.not_isUnit (R.squarefree p (by simpa only [pow_two] using hc))

theorem cubicThetaCoordinates_remove_primeCube {p n : Eisenstein} (hp : primaryPrime p)
    (R : CubicThetaCoordinates (n*p^3)) : Nonempty (CubicThetaCoordinates n) := by
  obtain ⟨d,hd⟩ := cubicThetaCoordinates_primeCube_dvd hp R
  have hdp : primary d := primary_of_mul hp.1 (hd ▸ R.cube_primary)
  refine ⟨{
    unit := R.unit
    order := R.order
    squarefreePart := R.squarefreePart
    cubePart := d
    squarefree_primary := R.squarefree_primary
    cube_primary := hdp
    squarefree := R.squarefree
    numerator_eq := ?_ }⟩
  apply mul_right_cancel₀ (pow_ne_zero 3 hp.2.ne_zero)
  calc
    n*p^3 = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
    _ = ((R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*d^3))*p^3 := by rw [hd]; ring

theorem cubicThetaCoordinates_primeCube_iff {p n : Eisenstein} (hp : primaryPrime p) :
    Nonempty (CubicThetaCoordinates (n*p^3)) ↔ Nonempty (CubicThetaCoordinates n) := by
  constructor
  · rintro ⟨R⟩
    exact cubicThetaCoordinates_remove_primeCube hp R
  · rintro ⟨R⟩
    exact ⟨R.mulPrimaryCube p hp.1⟩

theorem cubicThetaArithmeticCoefficient_primeCube {p : Eisenstein} (hp : primaryPrime p)
    (n : Eisenstein) :
    cubicThetaArithmeticCoefficient (n*p^3)=(norm p:ℂ)⁻¹*cubicThetaArithmeticCoefficient n := by
  classical
  by_cases hn : Nonempty (CubicThetaCoordinates n)
  · exact cubicThetaArithmeticCoefficient_mulPrimaryCube (Classical.choice hn) p hp.1
  · have hnp := mt (cubicThetaCoordinates_primeCube_iff hp).mp hn
    simp only [cubicThetaArithmeticCoefficient,dite_eq_right hn,dite_eq_right hnp,mul_zero]

theorem cubicThetaCuspCoefficient_primeCube {p : Eisenstein} (hp : primaryPrime p)
    (n : Eisenstein) (j : Fin 3) :
    cubicThetaCuspCoefficient j (n*p^3)=(norm p:ℂ)⁻¹*cubicThetaCuspCoefficient j n := by
  classical
  by_cases hn : Nonempty (CubicThetaCoordinates n)
  · exact cubicThetaCuspCoefficient_mulPrimaryCube (Classical.choice hn) p hp.1 j
  · have hnp := mt (cubicThetaCoordinates_primeCube_iff hp).mp hn
    simp only [cubicThetaCuspCoefficient,dite_eq_right hn,dite_eq_right hnp,mul_zero]

end CubicFirstMoment

end

end OAI
