import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSievePhase

namespace OAI

/-! The exact primary coefficient selector of DR v3 (5.17)--(5.18). -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaPrimarySupport (n : Eisenstein) : Prop :=
  ∃ R : CubicThetaCoordinates n, R.order = 1 ∧ (R.unit:Eisenstein) = 1

lemma cubicThetaPrimarySupport_coordinates {n : Eisenstein} (R : CubicThetaCoordinates n) :
    cubicThetaPrimarySupport n ↔ R.order = 1 ∧ (R.unit:Eisenstein) = 1 := by
  constructor
  · rintro ⟨S,hS⟩
    cases S.unique R
    exact hS
  · exact fun h => ⟨R,h⟩

/-- This is the source set S, written on the common numerator lattice. -/
lemma cubicThetaPrimarySupport_iff (n : Eisenstein) :
    cubicThetaPrimarySupport n ↔ ∃ c d : Eisenstein,
      primary c ∧ primary d ∧ Squarefree c ∧ n = lambdaE*c*d^3 := by
  constructor
  · rintro ⟨R,hk,hu⟩
    refine ⟨R.squarefreePart,R.cubePart,R.squarefree_primary,R.cube_primary,R.squarefree,?_⟩
    calc
      n = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
      _ = _ := by rw [hk,hu,pow_one,one_mul]; ring
  · rintro ⟨c,d,hc,hd,hs,hn⟩
    let R : CubicThetaCoordinates n := {
      unit := 1
      order := 1
      squarefreePart := c
      cubePart := d
      squarefree_primary := hc
      cube_primary := hd
      squarefree := hs
      numerator_eq := by simpa [mul_assoc] using hn }
    exact ⟨R,rfl,rfl⟩

def cubicThetaRootProjector (z : ℂ) : ℂ := (1+omega*z+omega^2*z^2)/3

lemma cubicThetaRootProjector_one : cubicThetaRootProjector 1 = 0 := by
  unfold cubicThetaRootProjector
  linear_combination (1/3:ℂ)*omega_quadratic

lemma cubicThetaRootProjector_omega : cubicThetaRootProjector omega = 0 := by
  unfold cubicThetaRootProjector
  have h4 : omega^4 = omega := by
    calc
      _ = omega^3*omega := by ring
      _ = _ := by rw [omega_cube,one_mul]
  have he : omega^2*omega^2 = omega^4 := by ring
  rw [he,h4]
  linear_combination (1/3:ℂ)*omega_quadratic

lemma cubicThetaRootProjector_omega_sq : cubicThetaRootProjector (omega^2) = 1 := by
  unfold cubicThetaRootProjector
  have h3 : omega*(omega^2) = 1 := by rw [←pow_succ',omega_cube]
  have h6 : omega^2*(omega^2)^2 = 1 := by
    calc
      _ = (omega^3)^2 := by ring
      _ = _ := by rw [omega_cube]; norm_num
  rw [h3,h6]
  norm_num

lemma CubicThetaCoordinates.primary_product {n : Eisenstein} (R : CubicThetaCoordinates n) :
    primary (R.squarefreePart*R.cubePart^3) := by
  have hp : primary (R.cubePart^3) := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
      primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary)
  exact primary_mul R.squarefree_primary hp

lemma cubicThetaRootProjector_coefficient {n : Eisenstein} (R : CubicThetaCoordinates n) :
    cubicThetaRootProjector (cubicThetaSievePhase n)*star R.coefficient =
      if cubicThetaPrimarySupport n then star R.coefficient else 0 := by
  rw [cubicThetaPrimarySupport_coordinates R]
  by_cases hA : R.order % 3 = 0 ∧ 3 ≤ R.order
  · have hn : ¬(R.order = 1 ∧ (R.unit:Eisenstein) = 1) := by omega
    rw [ite_eq_right hn,cubicThetaSievePhase_high R hA.2,cubicThetaRootProjector_one,zero_mul]
  · by_cases hB : R.order % 3 = 1 ∧ ((R.unit:Eisenstein) = 1 ∨ (R.unit:Eisenstein) = -1)
    · by_cases hk : R.order = 1
      · rcases hB.2 with hu | hu
        · have hn : n = lambdaE*(R.squarefreePart*R.cubePart^3) := by
            calc
              n = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
              _ = _ := by rw [hk,hu,pow_one,one_mul]
          have hp : cubicThetaSievePhase n = omega^2 := by
            rw [hn]
            exact cubicThetaSievePhase_primary R.primary_product
          rw [ite_eq_left ⟨hk,hu⟩,hp,cubicThetaRootProjector_omega_sq,one_mul]
        · have hu' : (R.unit:Eisenstein) ≠ 1 := by
            intro he
            have hc : (1:Eisenstein) ≠ -1 := by norm_num
            exact hc (he.symm.trans hu)
          have hn : n = -(lambdaE*(R.squarefreePart*R.cubePart^3)) := by
            calc
              n = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
              _ = _ := by rw [hk,hu,pow_one]; ring
          have hp : cubicThetaSievePhase n = omega := by
            rw [hn]
            exact cubicThetaSievePhase_negative_primary R.primary_product
          rw [ite_eq_right (by simp [hu']),hp,cubicThetaRootProjector_omega,zero_mul]
      · have hh : 3 ≤ R.order := by omega
        rw [ite_eq_right (by simp [hk]),cubicThetaSievePhase_high R hh,
          cubicThetaRootProjector_one,zero_mul]
    · have he : R.coefficient = 0 := by
        simp only [CubicThetaCoordinates.coefficient,ite_eq_right hA,ite_eq_right hB]
      rw [he,star_zero,mul_zero]
      split_ifs <;> rfl

/-- Multiplying the actual conjugate theta coefficient by the finite
third-root projector cuts it down to precisely the source set S. -/
theorem cubicThetaRootProjector_arithmetic (n : Eisenstein) :
    cubicThetaRootProjector (cubicThetaSievePhase n)*star (cubicThetaArithmeticCoefficient n) =
      if cubicThetaPrimarySupport n then star (cubicThetaArithmeticCoefficient n) else 0 := by
  by_cases h : Nonempty (CubicThetaCoordinates n)
  · let R := Classical.choice h
    rw [cubicThetaArithmeticCoefficient_formula R]
    exact cubicThetaRootProjector_coefficient R
  · have he : cubicThetaArithmeticCoefficient n = 0 := by
      simp only [cubicThetaArithmeticCoefficient,dite_eq_right h]
    rw [he,star_zero,mul_zero]
    split_ifs <;> rfl

end CubicFirstMoment

end

end OAI
