import Mathlib
import OAI.Probability.Perceptron.Variational.CompactGGEvents

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction NNReal ENNReal

section

variable {L : Type*} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]

def compactCodeArray (χ : CompactJointOverlap → L) (Q : CompactArray CompactJointOverlap) :
    FiniteOverlap L := fun i j => χ (Q i j)

def compactCodeBlock {n : ℕ} (χ : CompactJointOverlap → L) (Q : CompactBlock CompactJointOverlap n) :
    FiniteBlock L n := fun i j => χ (Q i j)

lemma compactCodeArray_measurable {L : Type*} [Fintype L] [MeasurableSpace L]
    [MeasurableSingletonClass L] {χ : CompactJointOverlap → L} (hχ : Measurable χ) :
    Measurable (compactCodeArray χ) := by
  unfold compactCodeArray
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hχ.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma compactCodeBlock_measurable {L : Type*} [Fintype L] [MeasurableSpace L]
    [MeasurableSingletonClass L] {χ : CompactJointOverlap → L} (hχ : Measurable χ) (n : ℕ) :
    Measurable (compactCodeBlock (n:=n) χ) := by
  unfold compactCodeBlock
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hχ.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma compactGG_finite_pushforward (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
    {χ : CompactJointOverlap → L} (hχ : Measurable χ) :
    FiniteGG ((μ : Measure (CompactArray CompactJointOverlap)).map (compactCodeArray χ)) := by
  classical
  intro n hn i A c
  have hm := compactCodeArray_measurable hχ
  have hb := finiteBlock_measurable (L:=L) n
  have he (a b : ℕ) : Measurable (fun R : FiniteOverlap L => R a b) := by fun_prop
  have hs : MeasurableSet {R : FiniteOverlap L | finiteBlock n R=A} :=
    measurableSet_eq_fun hb measurable_const
  have hv (a b : ℕ) : MeasurableSet {R : FiniteOverlap L | R a b=c} :=
    measurableSet_eq_fun (he a b) measurable_const
  have hvv (a b : ℕ) : MeasurableSet {R : FiniteOverlap L | finiteBlock n R=A ∧ R a b=c} := hs.inter (hv a b)
  rw [map_measureReal_apply hm (hvv _ _),map_measureReal_apply hm hs,
    map_measureReal_apply hm (hv 0 1)]
  simp_rw [map_measureReal_apply hm (hvv _ _)]
  exact compactGG_events μ n (by omega) i (hGG n i)
    ((compactCodeBlock χ) ⁻¹' {A}) ((measurableSet_singleton A).preimage (compactCodeBlock_measurable hχ n))
    (χ ⁻¹' {c}) ((measurableSet_singleton c).preimage hχ)

lemma compact_finite_code_block_unique [LinearOrder L]
    (μ ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGGμ : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
    (hGGν : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν n i f g=0)
    {χ : CompactJointOverlap → L} (hχ : Measurable χ) (d : L)
    (hμ : ∀ᵐ Q ∂(μ : Measure (CompactArray CompactJointOverlap)), (∀ i j, χ (Q i j)=χ (Q j i)) ∧
      (∀ i, χ (Q i i)=d) ∧ ∀ i j k, min (χ (Q i j)) (χ (Q i k)) ≤ χ (Q j k))
    (hν : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), (∀ i j, χ (Q i j)=χ (Q j i)) ∧
      (∀ i, χ (Q i i)=d) ∧ ∀ i j k, min (χ (Q i j)) (χ (Q i k)) ≤ χ (Q j k))
    (hpair : (μ : Measure (CompactArray CompactJointOverlap)).map (fun Q => χ (Q 0 1))=
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => χ (Q 0 1))) (n : ℕ) :
    (μ : Measure (CompactArray CompactJointOverlap)).map (fun Q => compactCodeBlock (n:=n+1) χ (compactBlock (n+1) Q))=
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => compactCodeBlock (n:=n+1) χ (compactBlock (n+1) Q)) := by
  let μ' := (μ : Measure (CompactArray CompactJointOverlap)).map (compactCodeArray χ)
  let ν' := (ν : Measure (CompactArray CompactJointOverlap)).map (compactCodeArray χ)
  have hm := compactCodeArray_measurable hχ
  have : IsProbabilityMeasure μ' := inferInstance
  have : IsProbabilityMeasure ν' := inferInstance
  have hgρ (ρ : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (hρ : ∀ᵐ Q ∂(ρ : Measure (CompactArray CompactJointOverlap)), (∀ i j, χ (Q i j)=χ (Q j i)) ∧
        (∀ i, χ (Q i i)=d) ∧ ∀ i j k, min (χ (Q i j)) (χ (Q i k)) ≤ χ (Q j k)) :
      ∀ᵐ R ∂(ρ : Measure (CompactArray CompactJointOverlap)).map (compactCodeArray χ), (∀ i j, R i j=R j i) ∧
        (∀ i, R i i=d) ∧ ∀ i j k, min (R i j) (R i k) ≤ R j k := by
    apply (ae_map_iff hm.aemeasurable (by measurability)).mpr
    exact hρ
  have hp : ∀ c, μ'.real {R | R 0 1=c}=ν'.real {R | R 0 1=c} := by
    intro c
    have hh := congrArg (fun ρ : Measure L => ρ.real {c}) hpair
    have he : Measurable (fun Q : CompactArray CompactJointOverlap => χ (Q 0 1)) := hχ.comp (by fun_prop)
    rw [map_measureReal_apply he (measurableSet_singleton c),
      map_measureReal_apply he (measurableSet_singleton c)] at hh
    change ((μ : Measure (CompactArray CompactJointOverlap)).map (compactCodeArray χ)).real {R | R 0 1=c} =
      ((ν : Measure (CompactArray CompactJointOverlap)).map (compactCodeArray χ)).real {R | R 0 1=c}
    rw [map_measureReal_apply hm (by measurability : MeasurableSet {R : FiniteOverlap L | R 0 1=c}),
      map_measureReal_apply hm (by measurability : MeasurableSet {R : FiniteOverlap L | R 0 1=c})]
    change (μ : Measure (CompactArray CompactJointOverlap)).real {Q | χ (Q 0 1)=c} =
      (ν : Measure (CompactArray CompactJointOverlap)).real {Q | χ (Q 0 1)=c}
    exact hh

  have he := finiteGG_block_law_unique μ' ν' d (hgρ μ hμ) (hgρ ν hν)
    (compactGG_finite_pushforward μ hGGμ hχ) (compactGG_finite_pushforward ν hGGν hχ) hp n
  dsimp only [μ',ν'] at he
  rw [Measure.map_map (finiteBlock_measurable (n+1)) hm,
    Measure.map_map (finiteBlock_measurable (n+1)) hm] at he
  have hf : finiteBlock (L:=L) (n+1) ∘ compactCodeArray χ =
      fun Q => compactCodeBlock (n:=n+1) χ (compactBlock (n+1) Q) := by
    funext Q i j
    rfl
  rw [hf] at he
  exact he

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def scaledStdGaussian (σ : ℝ) : Measure E := (stdGaussian E).map (σ • ·)

instance (σ : ℝ) : IsProbabilityMeasure (scaledStdGaussian (E := E) σ) :=
  inferInstanceAs (IsProbabilityMeasure ((stdGaussian E).map (σ • ·)))

lemma scaledStdGaussian_conv (σ τ : ℝ) :
    (scaledStdGaussian (E := E) σ) ∗ (scaledStdGaussian τ)=
      scaledStdGaussian (Real.sqrt (σ^2+τ^2)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv]
  simp only [scaledStdGaussian,charFun_map_smul,charFun_stdGaussian]
  rw [← Complex.exp_add]
  congr 1
  have hr : -‖σ • t‖^2/2 + -‖τ • t‖^2/2 = -‖Real.sqrt (σ^2+τ^2) • t‖^2/2 := by
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
      Real.sq_sqrt (add_nonneg (sq_nonneg σ) (sq_nonneg τ))]
    ring
  exact_mod_cast hr

lemma stdGaussian_integral_add {F : E → ℝ} (hF : Continuous F) (σ τ : ℝ)
    (hI : Integrable (fun y : E => F (Real.sqrt (σ^2+τ^2) • y)) (stdGaussian E)) :
    (∫ y, ∫ z, F (σ • y+τ • z) ∂stdGaussian E ∂stdGaussian E)=
      ∫ y, F (Real.sqrt (σ^2+τ^2) • y) ∂stdGaussian E := by
  have hi : Integrable F (scaledStdGaussian (E := E) (Real.sqrt (σ^2+τ^2))) := by
    exact (integrable_map_measure hF.aestronglyMeasurable (by fun_prop)).mpr hI
  rw [← scaledStdGaussian_conv σ τ] at hi
  have H := integral_conv hi
  rw [scaledStdGaussian_conv σ τ] at H
  simp only [scaledStdGaussian] at H
  rw [integral_map (by fun_prop) hF.aestronglyMeasurable] at H
  have hm : StronglyMeasurable (fun y : E => ∫ z : E, F (y+z) ∂(stdGaussian E).map (τ • ·)) :=
    ((hF.comp (continuous_fst.add continuous_snd)).stronglyMeasurable).integral_prod_right'
  rw [integral_map (by fun_prop) hm.aestronglyMeasurable] at H
  have HH : ∀ y : E, (∫ z, F (σ • y+z) ∂(stdGaussian E).map (τ • ·))=
      ∫ z, F (σ • y+τ • z) ∂stdGaussian E := by
    intro y
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [HH] at H
  exact H.symm

lemma gaussianEntropic_semigroup {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {p : ℝ} (hp : 0 ≤ p) (σ τ : ℝ) (x : E) :
    gaussianEntropic (stdGaussian E) p σ (gaussianEntropic (stdGaussian E) p τ f) x=
      gaussianEntropic (stdGaussian E) p (Real.sqrt (σ^2+τ^2)) f x := by
  have hfc := hf.continuous
  have hinner := gaussianEntropic_lipschitz (stdGaussian E) hf (σ := τ) hp
  by_cases hp0 : p=0
  · subst p
    rw [gaussianEntropic_zero _ hinner,gaussianEntropic_zero _ hf]
    simp_rw [gaussianEntropic_zero _ hf]
    have H := stdGaussian_integral_add (F := fun y => f (x+y)) (by fun_prop) σ τ
      (gaussian_integrable_lipschitz (stdGaussian E) hf _ x)
    simpa only [add_assoc] using H
  · rw [gaussianEntropic_pos _ hinner hp0,gaussianEntropic_pos _ hf hp0]
    have he (y : E) : Real.exp (p*gaussianEntropic (stdGaussian E) p τ f (x+σ • y))=
        ∫ z, Real.exp (p*f (x+σ • y+τ • z)) ∂stdGaussian E := by
      rw [gaussianEntropic_pos _ hf hp0]
      rw [mul_div_cancel₀ _ hp0]
      apply Real.exp_log
      exact mgf_pos (gaussian_integrable_exp_lipschitz (stdGaussian E) hf p τ _)
    simp_rw [he]
    have H := stdGaussian_integral_add (F := fun y => Real.exp (p*f (x+y))) (by fun_prop) σ τ
      (gaussian_integrable_exp_lipschitz (stdGaussian E) hf p _ x)
    simpa only [add_assoc] using congrArg (fun a : ℝ => Real.log a/p) H

lemma gaussianEntropic_variance_zero {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (p : ℝ) (x : E) :
    gaussianEntropic (stdGaussian E) p 0 f x=f x := by
  by_cases hp : p=0
  · subst p
    simp [gaussianEntropic_zero _ hf]
  · rw [gaussianEntropic_pos _ hf hp]
    simp [hp]

end SphericalPerceptronFreeEnergy

end

end OAI
