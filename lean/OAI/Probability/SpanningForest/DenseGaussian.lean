import OAI.Probability.SpanningForest.DenseBrownian

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Topology Matrix

namespace Problem336.DenseGaussian

variable {T Ω : Type*} [TopologicalSpace T] [FirstCountableTopology T] [MeasurableSpace Ω]
variable {P : Measure Ω} {X : T → Ω → ℝ}

theorem hasLaw_finite_of_dense [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : Set T} (hD : Dense D)
    (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (ν : (ι → T) → ProbabilityMeasure (EuclideanSpace ℝ ι))
    (hν : ∀ a, Continuous (fun t => charFun (ν t : Measure (EuclideanSpace ℝ ι)) a))
    (hd : ∀ t : ι → T, (∀ i, t i ∈ D) →
      HasLaw (fun ω => WithLp.toLp 2 (fun i => X (t i) ω)) (ν t : Measure (EuclideanSpace ℝ ι)) P)
    (t : ι → T) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => X (t i) ω)) (ν t : Measure (EuclideanSpace ℝ ι)) P := by
  classical
  have hm (s : ι → T) : Measurable
      (fun ω => WithLp.toLp 2 (fun i => X (s i) ω)) := by
    exact (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp
      (Measurable.of_eval (fun i => hX (s i)))
  refine ⟨(hm t).aemeasurable, ?_⟩
  apply Measure.ext_of_charFun
  funext a
  let F : (ι → T) → ℂ := fun s =>
    ∫ ω, Complex.exp ((inner (𝕜 := ℝ)
      (WithLp.toLp 2 (fun i => X (s i) ω)) a : ℂ) * Complex.I) ∂P
  have hF : Continuous F := by
    apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
    · intro s
      apply Measurable.aestronglyMeasurable
      simp only [PiLp.inner_apply]
      fun_prop
    · intro s
      exact Filter.Eventually.of_forall (fun ω => by
        rw [Complex.norm_exp_ofReal_mul_I])
    · exact integrable_const 1
    · filter_upwards [hc] with ω hω
      simp only [PiLp.inner_apply]
      have hi (i : ι) : Continuous (fun s : ι → T => X (s i) ω) :=
        hω.comp (continuous_apply i)
      fun_prop
  have hpi : Dense (Set.pi Set.univ (fun _ : ι => D)) :=
    dense_pi Set.univ (fun _ _ => hD)
  have heq : F = fun s => charFun (ν s : Measure (EuclideanSpace ℝ ι)) a := by
    apply Continuous.ext_on hpi hF (hν a)
    intro s hs
    have hlaw := hd s (fun i => hs i (Set.mem_univ i))
    simpa [F, charFun_apply] using hlaw.integral_comp
      (f := fun x : EuclideanSpace ℝ ι =>
        Complex.exp ((inner (𝕜 := ℝ) x a : ℂ) * Complex.I)) (by fun_prop)
  rw [charFun_apply, integral_map (hm t).aemeasurable (by fun_prop)]
  exact congrFun heq t

theorem hasLaw_brownian_finite_of_dense [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : T → ℝ≥0) (hτ : Continuous τ)
    {D : Set T} (hD : Dense D)
    (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hd : ∀ t : ι → T, (∀ i, t i ∈ D) →
      HasLaw (fun ω => WithLp.toLp 2 (fun i => X (t i) ω))
        (multivariateGaussian 0 (DenseBrownian.timeCovariance (τ ∘ t))) P)
    (t : ι → T) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => X (t i) ω))
      (multivariateGaussian 0 (DenseBrownian.timeCovariance (τ ∘ t))) P := by
  apply hasLaw_finite_of_dense hD hX hc
    (fun s => ⟨multivariateGaussian 0 (DenseBrownian.timeCovariance (τ ∘ s)),
      inferInstance⟩) ?_ hd t
  intro a
  simp only [ProbabilityMeasure.coe_mk]
  simp_rw [charFun_multivariateGaussian (DenseBrownian.timeCovariance_posSemidef _)]
  simp only [DenseBrownian.timeCovariance, Matrix.of_apply, Matrix.mulVec, dotProduct]
  fun_prop

variable [DecidableEq T]
omit [TopologicalSpace T] [FirstCountableTopology T]

theorem isGaussianProcess_of_finite_laws (τ : T → ℝ≥0)
    (h : ∀ I : Finset T,
      HasLaw (fun ω => WithLp.toLp 2 (fun i : I => X i.val ω))
        (multivariateGaussian 0 (DenseBrownian.timeCovariance (fun i : I => τ i.val))) P) :
    IsGaussianProcess X P := by
  classical
  constructor
  intro I
  exact (h I).hasGaussianLaw.map_equiv
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ))

theorem hasLaw_eval_of_finite_laws (τ : T → ℝ≥0)
    (h : ∀ I : Finset T,
      HasLaw (fun ω => WithLp.toLp 2 (fun i : I => X i.val ω))
        (multivariateGaussian 0 (DenseBrownian.timeCovariance (fun i : I => τ i.val))) P)
    (t : T) : HasLaw (X t) (gaussianReal 0 (τ t)) P := by
  classical
  have hlaw := (measurePreserving_eval_multivariateGaussian
    (DenseBrownian.timeCovariance_posSemidef (fun i : ({t} : Finset T) => τ i.val))
    (i := ⟨t, by simp⟩)).hasLaw.comp (h {t})
  simpa [DenseBrownian.timeCovariance, Function.comp_def] using hlaw

theorem integral_of_finite_laws (τ : T → ℝ≥0)
    (h : ∀ I : Finset T,
      HasLaw (fun ω => WithLp.toLp 2 (fun i : I => X i.val ω))
        (multivariateGaussian 0 (DenseBrownian.timeCovariance (fun i : I => τ i.val))) P)
    (t : T) : ∫ ω, X t ω ∂P = 0 := by
  simpa using (hasLaw_eval_of_finite_laws τ h t).integral_eq

theorem covariance_of_finite_laws (τ : T → ℝ≥0)
    (h : ∀ I : Finset T,
      HasLaw (fun ω => WithLp.toLp 2 (fun i : I => X i.val ω))
        (multivariateGaussian 0 (DenseBrownian.timeCovariance (fun i : I => τ i.val))) P)
    (s t : T) : cov[X s, X t; P] = min (τ s : ℝ) (τ t : ℝ) := by
  classical
  let I : Finset T := {s, t}
  let i : I := ⟨s, by simp [I]⟩
  let j : I := ⟨t, by simp [I]⟩
  have heq := (h I).covariance_fun_comp
    (f := fun x : EuclideanSpace ℝ I => x i)
    (g := fun x : EuclideanSpace ℝ I => x j)
    (by fun_prop) (by fun_prop)
  rw [covariance_eval_multivariateGaussian
    (DenseBrownian.timeCovariance_posSemidef _)] at heq
  exact heq

end Problem336.DenseGaussian

end

end OAI
