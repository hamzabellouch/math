import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmetic

namespace OAI

/-! Exact support coordinates at each unit and ramified power of a primary
frequency. Changing that unit or exponent preserves the squarefree/cube support. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaCoordinates.primary_power {h : Eisenstein} (hh : primary h)
    (e : Eisensteinˣ) (k : ℕ)
    (R : CubicThetaCoordinates ((e:Eisenstein)*lambdaE^k*h)) :
    R.unit=e ∧ R.order=k ∧ R.squarefreePart*R.cubePart^3=h := by
  have hp : primary (R.squarefreePart*R.cubePart^3) :=
    primary_mul R.squarefree_primary (by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
        primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary))
  exact unit_ramified_primary_unique hp hh R.numerator_eq.symm

theorem cubicThetaCoordinates_primary_power_iff {h : Eisenstein}
    (hh : primary h) (e : Eisensteinˣ) (k : ℕ) :
    Nonempty (CubicThetaCoordinates ((e:Eisenstein)*lambdaE^k*h)) ↔
      ∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ h=c*d^3 := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.squarefreePart,R.cubePart,R.squarefree_primary,R.cube_primary,
      R.squarefree,(R.primary_power hh e k).2.2.symm⟩
  · rintro ⟨c,d,hc,hd,hs,he⟩
    exact ⟨{
      unit := e
      order := k
      squarefreePart := c
      cubePart := d
      squarefree_primary := hc
      cube_primary := hd
      squarefree := hs
      numerator_eq := by rw [he] }⟩

theorem cubicThetaCoordinates_primary_support_iff {h : Eisenstein} (hh : primary h)
    (e f : Eisensteinˣ) (k j : ℕ) :
    Nonempty (CubicThetaCoordinates ((e:Eisenstein)*lambdaE^k*h)) ↔
      Nonempty (CubicThetaCoordinates ((f:Eisenstein)*lambdaE^j*h)) := by
  rw [cubicThetaCoordinates_primary_power_iff hh,cubicThetaCoordinates_primary_power_iff hh]

end CubicFirstMoment

end

end OAI
