import OAI.MathematicalPhysics.DefocusingNLS.Certificates.LaguerreProjection

namespace OAI

/-! # Polynomial test functions for the weighted differential equation -/

open Filter Topology MeasureTheory Set Polynomial

namespace DefocusingNLS

noncomputable def weightedPolynomialIntegrand (f : ℝ → ℂ) (p : ℂ[X]) (t : ℝ) : ℂ :=
  (Real.exp (-t) : ℂ) * f t * p.eval (t : ℂ)

noncomputable def weightedPolynomialIntegral (f : ℝ → ℂ) (p : ℂ[X]) : ℂ :=
  ∫ t in Ioi (0 : ℝ), weightedPolynomialIntegrand f p t

noncomputable def weightedPolynomialFunctional (f : ℝ → ℂ)
    (hf : ∀ p, IntegrableOn (weightedPolynomialIntegrand f p) (Ioi 0)) : ℂ[X] →ₗ[ℂ] ℂ where
  toFun := weightedPolynomialIntegral f
  map_add' p q := by
    unfold weightedPolynomialIntegral weightedPolynomialIntegrand
    simp only [Polynomial.eval_add, mul_add]
    exact integral_add (hf p) (hf q)
  map_smul' c p := by
    unfold weightedPolynomialIntegral weightedPolynomialIntegrand
    simp only [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1
    funext t
    ring

@[simp] theorem weightedPolynomialFunctional_apply (f : ℝ → ℂ)
    (hf : ∀ p, IntegrableOn (weightedPolynomialIntegrand f p) (Ioi 0)) (p : ℂ[X]) :
    weightedPolynomialFunctional f hf p = weightedPolynomialIntegral f p := rfl

theorem hasDerivAt_weightedPolynomialIntegrand (f f' : ℝ → ℂ) (p : ℂ[X]) (t : ℝ)
    (hf : HasDerivAt f (f' t) t) :
    HasDerivAt (weightedPolynomialIntegrand f p)
      (weightedPolynomialIntegrand f' p t +
        weightedPolynomialIntegrand f (p.derivative - p) t) t := by
  have he := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).ofReal_comp
  have hp := (p.hasDerivAt (t : ℂ)).comp_ofReal
  have h := (he.fun_mul hf).fun_mul hp
  convert! h using 1
  simp only [weightedPolynomialIntegrand, Polynomial.eval_sub,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one, Function.comp_apply]
  ring

theorem weightedPolynomialIntegral_derivative (f f' : ℝ → ℂ) (p : ℂ[X])
    (hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hc : ContinuousWithinAt f (Ici 0) 0)
    (hi : ∀ p, IntegrableOn (weightedPolynomialIntegrand f p) (Ioi 0))
    (hi' : IntegrableOn (weightedPolynomialIntegrand f' p) (Ioi 0)) :
    weightedPolynomialIntegral f' p + weightedPolynomialIntegral f (p.derivative - p) =
      -f 0 * p.eval 0 := by
  let D := fun t => weightedPolynomialIntegrand f' p t +
    weightedPolynomialIntegrand f (p.derivative - p) t
  have hD : IntegrableOn D (Ioi 0) := hi'.add (hi _)
  have hderiv (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      HasDerivAt (weightedPolynomialIntegrand f p) (D t) t :=
    hasDerivAt_weightedPolynomialIntegrand f f' p t (hd t ht)
  have hcont : ContinuousWithinAt (weightedPolynomialIntegrand f p) (Ici 0) 0 := by
    have hp : ContinuousWithinAt (fun t : ℝ => p.eval (t : ℂ)) (Ici 0) 0 :=
      ((p.hasDerivAt (0 : ℂ)).comp_ofReal).continuousAt.continuousWithinAt
    have he : ContinuousAt (fun t : ℝ => (Real.exp (-t) : ℂ)) 0 := by fun_prop
    exact (he.continuousWithinAt.mul hc).mul hp
  have hlim := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hderiv hD (hi p)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hD hlim
  dsimp only [D] at h
  rw [integral_add hi' (hi _)] at h
  simpa [weightedPolynomialIntegral, weightedPolynomialIntegrand] using h

/-- Symmetry of the Laguerre differential operator against a smooth function. -/
theorem weightedPolynomialIntegral_laguerre_operator (f f' f'' : ℝ → ℂ) (p : ℂ[X])
    (hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hd' : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f' (f'' t) t)
    (hc : ContinuousWithinAt f (Ici 0) 0)
    (hc' : ContinuousWithinAt f' (Ici 0) 0)
    (hi : ∀ p, IntegrableOn (weightedPolynomialIntegrand f p) (Ioi 0))
    (hi' : ∀ p, IntegrableOn (weightedPolynomialIntegrand f' p) (Ioi 0))
    (hi'' : ∀ p, IntegrableOn (weightedPolynomialIntegrand f'' p) (Ioi 0)) :
    weightedPolynomialIntegral f'' (X * p) +
      weightedPolynomialIntegral f' ((1 - X) * p) =
      weightedPolynomialIntegral f (laguerreOperator p) := by
  let F := weightedPolynomialFunctional f hi
  let F' := weightedPolynomialFunctional f' hi'
  let F'' := weightedPolynomialFunctional f'' hi''
  have h1 := weightedPolynomialIntegral_derivative f' f'' (X * p) hd' hc' hi' (hi'' _)
  have h2 := weightedPolynomialIntegral_derivative f f' (X * p.derivative) hd hc hi (hi' _)
  have he1 : (X * p).derivative - X * p - (1 - X) * p = X * p.derivative := by
    simp only [Polynomial.derivative_mul, Polynomial.derivative_X]
    ring
  have he2 : (X * p.derivative).derivative - X * p.derivative = laguerreOperator p := by
    simp only [Polynomial.derivative_mul, Polynomial.derivative_X, laguerreOperator]
    ring
  change F'' (X * p) + F' ((X * p).derivative - X * p) = _ at h1
  change F' (X * p.derivative) + F ((X * p.derivative).derivative - X * p.derivative) = _ at h2
  simp only [Polynomial.eval_mul, Polynomial.eval_X, zero_mul, mul_zero] at h1 h2
  rw [he2] at h2
  have h3 : F' ((X * p).derivative - X * p) - F' ((1 - X) * p) =
      F' (X * p.derivative) := by rw [← map_sub, he1]
  change F'' (X * p) + F' ((1 - X) * p) = F (laguerreOperator p)
  linear_combination h1 - h2 - h3

end DefocusingNLS

end OAI
