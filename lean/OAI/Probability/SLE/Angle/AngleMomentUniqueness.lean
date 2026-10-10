import OAI.Probability.SLE.Angle.AngleSpectralPairing
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

namespace OAI

/-! The cosine eigenpolynomials determine finite angle laws on [0, pi]. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Polynomial
open scoped Topology

namespace SLEExactGauge

private def angleIntegralLinear (μ : Measure ℝ) [IsFiniteMeasure μ] : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ θ, anglePolynomialTest p θ ∂μ
  map_add' p q := by
    simp only [anglePolynomialTest,eval_add]
    exact integral_add (anglePolynomialTest_integrable μ p) (anglePolynomialTest_integrable μ q)
  map_smul' c p := by
    simp only [anglePolynomialTest,eval_smul,smul_eq_mul,integral_const_mul,RingHom.id_apply]

lemma angle_polynomial_moments_of_eigen_moments (κ : ℝ)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ n, (∫ θ, anglePolynomialTest (angleEigenPolynomial κ n) θ ∂μ)=
      ∫ θ, anglePolynomialTest (angleEigenPolynomial κ n) θ ∂ν) (p : ℝ[X]) :
    (∫ θ, anglePolynomialTest p θ ∂μ)=∫ θ, anglePolynomialTest p θ ∂ν := by
  have he : angleIntegralLinear μ=angleIntegralLinear ν := by
    apply (angleEigenBasis κ).ext
    intro n
    change (∫ θ, anglePolynomialTest (angleEigenBasis κ n) θ ∂μ)=
      ∫ θ, anglePolynomialTest (angleEigenBasis κ n) θ ∂ν
    simpa only [angleEigenBasis_apply] using hm n
  exact congrArg (fun L : ℝ[X] →ₗ[ℝ] ℝ => L p) he

lemma angle_continuous_moments_of_polynomial_moments
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ p : ℝ[X], (∫ θ, anglePolynomialTest p θ ∂μ)=∫ θ, anglePolynomialTest p θ ∂ν)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ θ, g (Real.cos θ) ∂μ)=∫ θ, g (Real.cos θ) ∂ν := by
  let δ (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have hδ (j : ℕ) : 0<δ j := by dsimp [δ]; positivity
  have hδ1 (j : ℕ) : δ j≤1 := by
    dsimp [δ]
    apply (div_le_one (by positivity)).mpr
    have hj := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose p hp using fun j => exists_polynomial_near_of_continuousOn (-1) 1 g hg.continuousOn (δ j) (hδ j)
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).exists_bound_of_continuousOn hg.continuousOn
  have hc (θ : ℝ) : Real.cos θ∈Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩
  have hb (j : ℕ) (θ : ℝ) : ‖anglePolynomialTest (p j) θ‖≤M+1 := by
    change |(p j).eval (Real.cos θ)|≤M+1
    calc
      _ = |((p j).eval (Real.cos θ)-g (Real.cos θ))+g (Real.cos θ)| := by ring_nf
      _ ≤ |(p j).eval (Real.cos θ)-g (Real.cos θ)|+|g (Real.cos θ)| := abs_add_le _ _
      _ ≤ δ j+M := add_le_add (hp j _ (hc θ)).le (hM _ (hc θ))
      _ ≤ M+1 := by linarith [hδ1 j]
  have hl (θ : ℝ) : Tendsto (fun j => anglePolynomialTest (p j) θ) atTop (𝓝 (g (Real.cos θ))) := by
    have hh := squeeze_zero_norm (f := fun j => (p j).eval (Real.cos θ)-g (Real.cos θ))
      (fun j => by simpa only [Real.norm_eq_abs] using (hp j _ (hc θ)).le) hδlim
    simpa only [sub_add_cancel,zero_add,anglePolynomialTest] using hh.add_const (g (Real.cos θ))
  have hi (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
      Tendsto (fun j => ∫ θ, anglePolynomialTest (p j) θ ∂ρ) atTop (𝓝 (∫ θ, g (Real.cos θ) ∂ρ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => M+1)
      (fun j => (anglePolynomialTest_integrable ρ (p j)).aestronglyMeasurable)
      (integrable_const _) (fun j => Eventually.of_forall (hb j)) (Eventually.of_forall hl)
  apply tendsto_nhds_unique (hi μ)
  exact (hi ν).congr' (Eventually.of_forall fun j => (hm (p j)).symm)

lemma angleMeasures_eq_of_eigenMoments (κ : ℝ)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ θ ∂μ, θ∈Icc (0:ℝ) Real.pi) (hν : ∀ᵐ θ ∂ν, θ∈Icc (0:ℝ) Real.pi)
    (hm : ∀ n, (∫ θ, anglePolynomialTest (angleEigenPolynomial κ n) θ ∂μ)=
      ∫ θ, anglePolynomialTest (angleEigenPolynomial κ n) θ ∂ν) : μ=ν := by
  have hpoly := angle_polynomial_moments_of_eigen_moments κ μ ν hm
  have hcos : μ.map Real.cos=ν.map Real.cos := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map Real.continuous_cos.measurable.aemeasurable
      (show AEStronglyMeasurable (fun x => f x) (μ.map Real.cos) from f.continuous.aestronglyMeasurable),
      integral_map Real.continuous_cos.measurable.aemeasurable
      (show AEStronglyMeasurable (fun x => f x) (ν.map Real.cos) from f.continuous.aestronglyMeasurable)]
    exact angle_continuous_moments_of_polynomial_moments μ ν hpoly f f.continuous
  have hrecover (ρ : Measure ℝ) (hρ : ∀ᵐ θ ∂ρ, θ∈Icc (0:ℝ) Real.pi) :
      (ρ.map Real.cos).map Real.arccos=ρ := by
    rw [Measure.map_map Real.continuous_arccos.measurable Real.continuous_cos.measurable]
    have he : Real.arccos ∘ Real.cos =ᵐ[ρ] id := by
      filter_upwards [hρ] with θ hθ
      exact Real.arccos_cos hθ.1 hθ.2
    rw [Measure.map_congr he,Measure.map_id]
  rw [← hrecover μ hμ,hcos,hrecover ν hν]

end SLEExactGauge

end

end OAI
