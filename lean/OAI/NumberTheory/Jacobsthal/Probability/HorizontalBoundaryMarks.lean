import OAI.NumberTheory.Jacobsthal.Harmonic.RealAlgebraicFibers

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection

theorem horizontalLine_ne_zero (z : ℂ) : affineLine 0 z ≠ 0 := by
  intro hz
  have h := congrArg (MvPolynomial.eval ![(0 : ℂ),z+1]) hz
  simp [affineLine] at h

theorem nonlinear_not_dvd_horizontal (Q : MV ℂ) (hdeg : 1 < Q.totalDegree) (z : ℂ) :
    ¬Q ∣ affineLine 0 z := by
  intro hdiv
  have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv (horizontalLine_ne_zero z)
  exact (not_le_of_gt hdeg) (hd.trans (affineLine_degree_le 0 z))

def boundaryAbscissae (Q : MV ℝ) (y : ℝ) : Set ℝ := {x | peval Q x y = 0}

theorem boundary_abscissae_bound (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (y : ℝ) :
    (boundaryAbscissae Q y).Finite ∧ (boundaryAbscissae Q y).ncard ≤ 2*Q.totalDegree := by
  have hd : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  obtain ⟨hfin,hcard⟩ := irreducible_abscissa_bound (complexify Q) (affineLine 0 (y : ℂ)) hQ hd
    (nonlinear_not_dvd_horizontal _ hd y)
  have hpre := finite_real_preimage (intersectionAbscissae (complexify Q) (affineLine 0 (y : ℂ))) hfin
  have hsub : boundaryAbscissae Q y ⊆
      Complex.ofReal ⁻¹' intersectionAbscissae (complexify Q) (affineLine 0 (y : ℂ)) := by
    intro x hx
    refine ⟨((x : ℂ),(y : ℂ)),⟨?_,?_⟩,rfl⟩
    · rw [complexify_eval,← peval_eq_eval_pair]
      change peval Q x y = 0 at hx
      rw [hx,Complex.ofReal_zero]
    · simp [affineLine]
  refine ⟨hpre.1.subset hsub,?_⟩
  calc
    _ ≤ (Complex.ofReal ⁻¹' intersectionAbscissae (complexify Q) (affineLine 0 (y : ℂ))).ncard :=
      ncard_le_ncard hsub hpre.1
    _ ≤ _ := hpre.2
    _ ≤ _ := hcard
    _ ≤ 2*(complexify Q).totalDegree*1 := Nat.mul_le_mul_left _ (affineLine_degree_le 0 y)
    _ = 2*Q.totalDegree := by rw [mul_one,complexify_totalDegree]

end ErdosAlgebraicCurve

end

end Erdos970

end OAI
