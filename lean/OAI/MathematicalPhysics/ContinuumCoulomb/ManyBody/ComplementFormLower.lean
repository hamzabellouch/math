import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorFormDecomposition
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronFormDecomposition

namespace OAI

/-! Absorbing the actual one-body and Coulomb mixed forms into a positive
complement gap. All finite-rank and complement estimates remain explicit. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem sum_mixed_square_bound {a b A B p q t : ℝ}
    (_hp : 0 ≤ p) (_hq : 0 ≤ q) (ha : a^2 ≤ A*p*q) (hb : b^2 ≤ B*p*q) :
    (a+t*b)^2 ≤ 2*(A+t^2*B)*p*q := by
  have ht := mul_le_mul_of_nonneg_left hb (sq_nonneg t)
  nlinarith only [ha,ht,sq_nonneg (a-t*b)]

theorem complement_scalar_lower {F P Q a g C p q c : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hg : 0 < g) (hC : 0 ≤ C)
    (hm : P+Q+2*c ≤ F) (hP : a*p ≤ P) (hQ : (a+g)*q ≤ Q)
    (hc : c^2 ≤ C*p*q) :
    (a-C/g)*(p+q) ≤ F := by
  have ha := absorb_cross_term hC hp hq hg hc
  have he : 0 ≤ (C/g)*q := mul_nonneg (div_nonneg hC hg.le) hq
  nlinarith only [hm,hP,hQ,ha,he]

theorem interacting_complement_lower {n : ℕ}
    (V : Configuration n → ℝ) (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B)
    (p q : Coulomb.H1Vector n) (E a g A K t : ℝ)
    (hg : 0 < g) (hA : 0 ≤ A) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hfinite : (E+a)*Coulomb.mass p ≤ boundedPotentialForm V p+t*Coulomb.pairEnergy p)
    (hcomp : (E+a+g)*Coulomb.mass q ≤ boundedPotentialForm V q)
    (hkin : Coulomb.kinetic p ≤ K*Coulomb.mass p)
    (hcross : (graphBoundedCross (BoundedPotential.operator V hV B hB)
      (h1Coordinates p) (h1Coordinates q))^2 ≤ A*Coulomb.mass p*Coulomb.mass q) :
    (E+a-(2*(A+t^2*(8*(n:ℝ)^3*K)))/g)*(Coulomb.mass p+Coulomb.mass q) ≤
      boundedPotentialForm V (p.add q)+t*Coulomb.pairEnergy (p.add q) := by
  have hr := repulsionCross_square_bound p q
  have hk := mul_le_mul_of_nonneg_left hkin (by positivity : 0 ≤ 8*(n:ℝ)^3)
  have hr' : (repulsionCross p q)^2 ≤ (8*(n:ℝ)^3*K)*Coulomb.mass p*Coulomb.mass q := by
    apply hr.trans
    have h := mul_le_mul_of_nonneg_right hk (Coulomb.mass_nonneg q)
    convert h using 1
    ring
  have hc := sum_mixed_square_bound (t := t) (Coulomb.mass_nonneg p) (Coulomb.mass_nonneg q) hcross hr'
  have hq := mul_nonneg ht (Coulomb.pairEnergy_nonneg q)
  apply complement_scalar_lower (a := E+a) (g := g) (C := 2*(A+t^2*(8*(n:ℝ)^3*K)))
    (Q := boundedPotentialForm V q+t*Coulomb.pairEnergy q)
    (Coulomb.mass_nonneg p) (Coulomb.mass_nonneg q) hg (by positivity) _ hfinite _ hc
  · rw [boundedPotentialForm_add V hV B hB p q,pairEnergy_add p q]
    ring_nf
    exact le_rfl
  · linarith only [hcomp,hq]

end ContinuumCoulomb

end

end OAI
