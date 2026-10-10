import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalTermDerivative

namespace OAI

/-! Termwise differentiation of the actual fixed-angular theta series.
The derivative bound is uniform along each horizontal line. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaAngular_horizontal_hasDerivAt {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hv : 0<v) (h z : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ =>
      cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z+(u:ℂ)*h,v))
      (∑' n : Eisenstein,(2*Real.pi*Complex.I*(tracePair (cubicThetaFrequency n) h:ℂ))*
        cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) (z+(t:ℂ)*h) v n) t := by
  let K := (4*Real.pi*‖h‖)*(C*cubicWhittakerPowerConstant (ℓ.natAbs+1+3)*
    (9:ℝ)^(ℓ.natAbs+1)*81^(7/3:ℝ)*v^(4/3-2*(((ℓ.natAbs+1:ℕ):ℝ)+3)))
  let u : Eisenstein → ℝ := fun n => K*norm n^(-4/3:ℝ)
  have hu : Summable u := by
    simpa only [u,neg_div] using
      (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ)<4/3)).mul_left K
  let g (n : Eisenstein) (s : ℝ) :=
    cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) (z+(s:ℂ)*h) v n
  let g' (n : Eisenstein) (s : ℝ) :=
    (2*Real.pi*Complex.I*(tracePair (cubicThetaFrequency n) h:ℂ))*g n s
  have hd (n : Eisenstein) (s : ℝ) : HasDerivAt (g n) (g' n s) s :=
    cubicThetaSeriesTerm_horizontal_hasDerivAt _ h z v n s
  have hb (n : Eisenstein) (s : ℝ) : ‖g' n s‖≤u n := by
    exact cubicThetaAngular_horizontal_term_bound hC ha ℓ hv h (z+(s:ℂ)*h) n
  have hg0 : Summable (fun n => g n t) :=
    cubicThetaAngular_summable hC ha ℓ hv (z+(t:ℂ)*h)
  exact hasDerivAt_tsum hu hd hb hg0 t

theorem cubicThetaAngular_horizontal_deriv {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hv : 0<v) (h z : ℂ) (t : ℝ) :
    deriv (fun u : ℝ =>
      cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z+(u:ℂ)*h,v)) t=
      ∑' n : Eisenstein,(2*Real.pi*Complex.I*(tracePair (cubicThetaFrequency n) h:ℂ))*
        cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) (z+(t:ℂ)*h) v n :=
  (cubicThetaAngular_horizontal_hasDerivAt hC ha ℓ hv h z t).deriv

end CubicFirstMoment

end

end OAI
