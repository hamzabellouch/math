import OAI.MathematicalPhysics.Transonic.Exterior.BarrierPolynomial

namespace OAI

section
noncomputable section
namespace SepticProfile.FixedInterval

def signBox (n : ℕ) (a : Box) : Box := ⟨(-1)^n*a.center,a.radius⟩

lemma holds_signBox {Q : ℤ} {a : Box} {x : ℝ} (ha : Holds Q a x) (n : ℕ) :
    Holds Q (signBox n a) ((-1)^n*x) := by
  simp only [Holds,signBox,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one]
  rw [show (Q:ℝ)*((-1)^n*x)-(-1)^n*a.center=(-1)^n*((Q:ℝ)*x-a.center) by ring,
    abs_mul,abs_pow]
  simpa [Holds] using ha

end SepticProfile.FixedInterval
namespace SepticProfile.ExteriorPolynomial
open Polynomial PowerSeries

def reflectedTrunc (u : PowerSeries ℝ) (d : ℝ) : ℝ[X] :=
  PowerSeries.trunc 74 (PowerSeries.rescale (-d) (ExteriorJet.scaledReflected u))

def lowerPoly (u : PowerSeries ℝ) (d : ℝ) : ℝ[X] := 1-reflectedTrunc u d

lemma coeff_reflectedTrunc (u : PowerSeries ℝ) (d : ℝ) (n : ℕ) :
    (reflectedTrunc u d).coeff n=
      if n<74 then (-1)^n*(PowerSeries.coeff n (ExteriorJet.scaledReflected u)*d^n) else 0 := by
  simp only [reflectedTrunc,PowerSeries.coeff_trunc,PowerSeries.coeff_rescale]
  split_ifs with hn
  · rw [show -d=(-1)*d by ring,mul_pow];ring
  · rfl

lemma reflectedTrunc_zero (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1) (d : ℝ) :
    (reflectedTrunc u d).coeff 0=0 := by
  rw [coeff_reflectedTrunc];simp [ExteriorJet.scaledReflected_zero hu0]

lemma reflectedTrunc_degree (u : PowerSeries ℝ) (d : ℝ) :
    (reflectedTrunc u d).degree<74 := by
  exact PowerSeries.degree_trunc_lt _ _

lemma reflectedTrunc_natDegree (u : PowerSeries ℝ) (d : ℝ) :
    (reflectedTrunc u d).natDegree≤73 := by
  have h := reflectedTrunc_degree u d
  by_cases hz : reflectedTrunc u d=0
  · simp [hz]
  · rw [degree_eq_natDegree hz] at h
    norm_cast at h
    omega

lemma lowerPoly_coeff (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1)
    (d : ℝ) (n : ℕ) : (lowerPoly u d).coeff n=
      if n=0 then 1 else -(reflectedTrunc u d).coeff n := by
  simp only [lowerPoly,Polynomial.coeff_sub,Polynomial.coeff_one]
  split_ifs with hn
  · subst n;rw [reflectedTrunc_zero u hu0 d];ring
  · ring

end SepticProfile.ExteriorPolynomial

end
end

end OAI
