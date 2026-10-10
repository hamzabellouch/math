import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridDifferentiation

namespace OAI

/-! The actual, absolutely convergent Eisenstein series satisfies the
hyperbolic spectral equation on Re(s)>2. The two spatial differentiations
are justified by the proved local summable bounds. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisenstein_eigenvalue (s : ℂ) (hs : 2<s.re) (x y : ℝ)
    {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaEisenstein (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaEisenstein (cubicThetaCartesianPoint x y v) s := by
  have hx := cubicThetaEisensteinGrid_coordinate_derivs .x s hs x y hv
  have hy := cubicThetaEisensteinGrid_coordinate_derivs .y s hs x y hv
  have ht := cubicThetaEisensteinGrid_coordinate_derivs .height s hs x y hv
  dsimp only [cubicThetaCoordinateLine,cubicThetaCoordinateCenter] at hx hy ht
  let F := fun cd : Eisenstein × Eisenstein => fun a b t =>
    cubicThetaEisensteinGridTerm cd (cubicThetaCartesianPoint a b t) s
  have hsA : Summable (fun cd => (v:ℂ)^2*
      (deriv (deriv (fun t => F cd t y v)) x+
       deriv (deriv (fun t => F cd x t v)) y+
       deriv (deriv (fun t => F cd x y t)) v)) :=
    ((hx.2.2.2.add hy.2.2.2).add ht.2.2.2).mul_left _
  have hsB : Summable (fun cd => (v:ℂ)*deriv (fun t => F cd x y t) v) :=
    ht.2.2.1.mul_left _
  have he : (fun a b t => cubicThetaEisenstein (cubicThetaCartesianPoint a b t) s)=
      (fun a b t => ∑' cd, F cd a b t) := by
    funext a b t
    exact cubicThetaEisenstein_eq_grid _ _
  rw [he,cubicThetaEisenstein_eq_grid]
  unfold cubicThetaHyperbolicOperator
  change (v:ℂ)^2*(deriv (deriv (fun t => ∑' cd, F cd t y v)) x+
      deriv (deriv (fun t => ∑' cd, F cd x t v)) y+
      deriv (deriv (fun t => ∑' cd, F cd x y t)) v)-
        (v:ℂ)*deriv (fun t => ∑' cd, F cd x y t) v=
      s*(s-2)*(∑' cd, F cd x y v)
  rw [hx.2.1,hy.2.1,ht.2.1,ht.1]
  calc
    _ = ∑' cd, cubicThetaHyperbolicOperator (F cd) x y v := by
      unfold cubicThetaHyperbolicOperator
      rw [hsA.tsum_sub hsB,tsum_mul_left,tsum_mul_left,
        (hx.2.2.2.add hy.2.2.2).tsum_add ht.2.2.2,hx.2.2.2.tsum_add hy.2.2.2]
    _ = ∑' cd, s*(s-2)*F cd x y v := by
      apply tsum_congr
      intro cd
      exact cubicThetaEisensteinGrid_eigenvalue cd.1 cd.2 s x y hv
    _ = _ := tsum_mul_left

end CubicFirstMoment

end

end OAI
