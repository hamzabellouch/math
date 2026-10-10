import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ContinuousSobolevFirstDerivative

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def scaledLowerCoefficient (k : ℕ) (f χ : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) (r : ℝ) : 𝓢(E, ℂ) :=
  (hχc.mul_right (f' := fun x => (r : ℂ) ^ k * f (p + r • x))).toSchwartzMap
    (hχ.mul (contDiff_const.mul
      (hf.comp (contDiff_const.add (contDiff_const.smul contDiff_id)))))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma scaledLowerCoefficient_tendsto (k : ℕ) (hk : k ≠ 0) (f χ : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) :
    Tendsto (scaledLowerCoefficient k f χ hf hχ hχc p) (𝓝 0) (𝓝 0) := by
  apply tendsto_schwartz_of_common_support _ ?_ (tsupport χ) hχc ?_ ?_
  · change ContDiff ℝ ∞ (fun z : ℝ × E => χ z.2 * ((z.1 : ℂ) ^ k * f (p + z.1 • z.2)))
    exact (hχ.comp contDiff_snd).mul
      (((Complex.ofRealCLM.contDiff.comp contDiff_fst).pow k).mul
        (hf.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))))
  · intro r
    exact tsupport_mul_subset_left
  · ext x
    simp [scaledLowerCoefficient, hk]

lemma scaledLowerCoefficient_sobolev_tendsto (k : ℕ) (hk : k ≠ 0) (f χ : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (p : E) (s : ℝ) :
    Tendsto (fun r => schwartzToSobolev s (scaledLowerCoefficient k f χ hf hχ hχc p r))
      (𝓝 0) (𝓝 0) := by
  simpa only [map_zero, Function.comp_def] using! (schwartzToSobolev s).continuous.continuousAt.tendsto.comp
    (scaledLowerCoefficient_tendsto k hk f χ hf hχ hχc p)

def sobolevCoefficientOperator {I : Type*} [Fintype I] {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * (s - 2))
    (D : I → FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s - 2))
    (a : I → FourierSobolevSpace E ℂ (s - 2)) :
    FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s - 2) :=
  ∑ i, (sobolevProduct hs (a i)) ∘L D i

lemma norm_sobolevCoefficientOperator_le {I : Type*} [Fintype I] {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * (s - 2))
    (D : I → FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s - 2))
    (a : I → FourierSobolevSpace E ℂ (s - 2)) :
    ‖sobolevCoefficientOperator hs D a‖ ≤
      sobolevAlgebraConstant (E := E) (s - 2) * ∑ i, ‖a i‖ * ‖D i‖ := by
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [sobolevAlgebraConstant_nonneg (E := E) (s - 2)])
  intro u
  exact sobolevProduct_bound hs _ _

lemma sobolevCoefficientOperator_tendsto {I : Type*} [Fintype I] {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * (s - 2))
    (D : I → FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s - 2))
    (a : ℝ → I → FourierSobolevSpace E ℂ (s - 2))
    (ha : ∀ i, Tendsto (fun r => a r i) (𝓝 0) (𝓝 0)) :
    Tendsto (fun r => sobolevCoefficientOperator hs D (a r)) (𝓝 0) (𝓝 0) := by
  have hh (i : I) : Tendsto (fun r => (sobolevProduct hs (a r i)) ∘L D i) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun B : FourierSobolevSpace E ℂ (s - 2) →L[ℂ]
        FourierSobolevSpace E ℂ (s - 2) => B ∘L D i) := by fun_prop
    simpa only [map_zero, ContinuousLinearMap.zero_comp, Function.comp_def] using!
      hc.continuousAt.tendsto.comp
        ((sobolevProduct hs).continuous.continuousAt.tendsto.comp (ha i))
  simpa only [sobolevCoefficientOperator, Finset.sum_const_zero] using! tendsto_finsetSum Finset.univ (fun i _ => hh i)

lemma sobolevCoefficientOperator_representative {I : Type*} [Fintype I] {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * (s - 2))
    (D : I → FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s - 2))
    (a : I → FourierSobolevSpace E ℂ (s - 2)) (u : FourierSobolevSpace E ℂ s) :
    sobolevRepresentative hs (sobolevCoefficientOperator hs D a u) =
      ∑ i, sobolevRepresentative hs (a i) * sobolevRepresentative hs (D i u) := by
  simp only [sobolevCoefficientOperator, sum_apply, ContinuousLinearMap.comp_apply,
    map_sum, sobolevRepresentative_product]

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sobolevFirstLower (s : ℝ) (v : E) :
    FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s :=
  sobolevInclusion (s + 2 - 1) s (by linarith) ∘L sobolevDerivative (s + 2) v

lemma sobolevFirstLower_representative (s : ℝ) (v : E)
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * (s + 2))
    (u : FourierSobolevSpace E ℂ (s + 2)) (x : E) :
    sobolevRepresentative hs (sobolevFirstLower s v u) x =
      fderiv ℝ (sobolevRepresentative ht u : E → ℂ) x v := by
  have hl : Module.finrank ℝ E < 2 * (s + 2 - 1) := by linarith
  rw [sobolevFirstLower, ContinuousLinearMap.comp_apply,
    sobolevInclusion_representative _ _ _ hl hs]
  exact sobolevDerivative_representative hl ht u v x

def coefficientPerturbation {ι : Type*} [Fintype ι] (b : ι → E) {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s)
    (a : ι → ι → FourierSobolevSpace E ℂ s) (c : ι → FourierSobolevSpace E ℂ s) :
    FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s :=
  (∑ i, ∑ j, (sobolevProduct hs (a i j)) ∘L sobolevSecondDerivative (s + 2) (b i) (b j)) +
    ∑ i, (sobolevProduct hs (c i)) ∘L sobolevFirstLower s (b i)

lemma coefficientPerturbation_tendsto {ι : Type*} [Fintype ι] (b : ι → E) {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s)
    (a : ℝ → ι → ι → FourierSobolevSpace E ℂ s)
    (c : ℝ → ι → FourierSobolevSpace E ℂ s)
    (ha : ∀ i j, Tendsto (fun r => a r i j) (𝓝 0) (𝓝 0))
    (hc : ∀ i, Tendsto (fun r => c r i) (𝓝 0) (𝓝 0)) :
    Tendsto (fun r => coefficientPerturbation b hs (a r) (c r)) (𝓝 0) (𝓝 0) := by
  have hmul {a : ℝ → FourierSobolevSpace E ℂ s} (ha : Tendsto a (𝓝 0) (𝓝 0))
      (D : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s) :
      Tendsto (fun r => (sobolevProduct hs (a r)) ∘L D) (𝓝 0) (𝓝 0) := by
    have hcomp : Continuous (fun B : FourierSobolevSpace E ℂ s →L[ℂ]
        FourierSobolevSpace E ℂ s => B ∘L D) := by fun_prop
    simpa only [map_zero, ContinuousLinearMap.zero_comp, Function.comp_def] using!
      hcomp.continuousAt.tendsto.comp ((sobolevProduct hs).continuous.continuousAt.tendsto.comp ha)
  simpa only [coefficientPerturbation, Finset.sum_const_zero, add_zero] using!
    (tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_finsetSum Finset.univ (fun j _ => hmul (ha i j) _))).add
      (tendsto_finsetSum Finset.univ (fun i _ => hmul (hc i) _))

lemma coefficientPerturbation_representative {ι : Type*} [Fintype ι] (b : ι → E) {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * (s + 2))
    (a : ι → ι → FourierSobolevSpace E ℂ s) (c : ι → FourierSobolevSpace E ℂ s)
    (u : FourierSobolevSpace E ℂ (s + 2)) (x : E) :
    sobolevRepresentative hs (coefficientPerturbation b hs a c u) x =
      (∑ i, ∑ j, sobolevRepresentative hs (a i j) x *
        fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b j)) x (b i)) +
      ∑ i, sobolevRepresentative hs (c i) x *
        fderiv ℝ (sobolevRepresentative ht u : E → ℂ) x (b i) := by
  have hd (i j : ι) : sobolevRepresentative hs
      (sobolevSecondDerivative (s + 2) (b i) (b j) u) x =
      fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b j)) x (b i) := by
    have hh := sobolevSecondDerivative_representative
      (s := s + 2) (show Module.finrank ℝ E < 2 * (s + 2 - 2) by linarith)
      ht u (b i) (b j) x
    rw [sobolevRepresentative_congr (s + 2 - 2) s (by ring) _ hs] at hh
    exact hh
  simp only [coefficientPerturbation, _root_.add_apply, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sum,
    BoundedContinuousFunction.add_apply, BoundedContinuousFunction.sum_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [sobolevRepresentative_product, BoundedContinuousFunction.mul_apply, hd]
  · apply Finset.sum_congr rfl
    intro i _
    rw [sobolevRepresentative_product, BoundedContinuousFunction.mul_apply,
      sobolevFirstLower_representative s _ hs ht]


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]
variable (b : Module.Basis ι ℝ E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)

def rescaledDifferentialPerturbation (r : ℝ) :
    FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s :=
  coefficientPerturbation b hs
    (fun i j => schwartzToSobolev s (rescaledCoefficient (fun x => (a i j x : ℂ)) χ
      (Complex.ofRealCLM.contDiff.comp (ha i j)) hχ hχc p r))
    (fun i => schwartzToSobolev s (scaledLowerCoefficient 1 (fun x => (c i x : ℂ)) χ
      (Complex.ofRealCLM.contDiff.comp (hc i)) hχ hχc p r))

lemma rescaledDifferentialPerturbation_tendsto :
    Tendsto (rescaledDifferentialPerturbation b a c ha hc χ hχ hχc p hs) (𝓝 0) (𝓝 0) := by
  apply coefficientPerturbation_tendsto
  · intro i j
    exact rescaledCoefficient_sobolev_tendsto _ _ _ _ _ _ _
  · intro i
    exact scaledLowerCoefficient_sobolev_tendsto 1 (by norm_num) _ _ _ _ _ _ _

lemma rescaledDifferentialPerturbation_representative (r : ℝ)
    (ht : Module.finrank ℝ E < 2 * (s + 2)) (u : FourierSobolevSpace E ℂ (s + 2)) (x : E)
    (hχx : χ x = 1) :
    sobolevRepresentative hs (rescaledDifferentialPerturbation b a c ha hc χ hχ hχc p hs r u) x =
      (∑ i, ∑ j, ((a i j (p + r • x) : ℂ) - (a i j p : ℂ)) *
        fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b j)) x (b i)) +
      (r : ℂ) * ∑ i, (c i (p + r • x) : ℂ) *
        fderiv ℝ (sobolevRepresentative ht u : E → ℂ) x (b i) := by
  rw [rescaledDifferentialPerturbation, coefficientPerturbation_representative _ hs ht]
  simp only [sobolevRepresentative_schwartz, SchwartzMap.toBoundedContinuousFunction_apply]
  change (∑ i, ∑ j, (χ x * ((a i j (p + r • x) : ℂ) - (a i j p : ℂ))) * _) +
    ∑ i, (χ x * ((r : ℂ) ^ 1 * (c i (p + r • x) : ℂ))) * _ = _
  simp only [hχx, one_mul, pow_one, mul_assoc, ← Finset.mul_sum]

include ha hc hχ hχc in

theorem exists_rescaled_local_inverse (hA : Matrix.PosDef (fun i j => a i j p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r| < ε → ∀ α : ℝ, 1 ≤ α →
      ∃ R : FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s + 2),
        ‖R‖ ≤ 2 * @anisotropicConstant E (QuadraticInnerSpace (fun i j => a i j p) hA) _ _
          (QuadraticInnerSpace.instNormedAddCommGroup _ hA)
          (QuadraticInnerSpace.instInnerProductSpaceReal _ hA)
          (physicalQuadraticEquiv b (fun i j => a i j p) hA) ∧
        (∀ f, ‖sobolevInclusion (s + 2) (s + 1) (by linarith) (R f)‖ ≤
          2 * (@anisotropicConstant E (QuadraticInnerSpace (fun i j => a i j p) hA) _ _
          (QuadraticInnerSpace.instNormedAddCommGroup _ hA)
          (QuadraticInnerSpace.instInnerProductSpaceReal _ hA)
          (physicalQuadraticEquiv b (fun i j => a i j p) hA) *
            (Real.sqrt α)⁻¹) * ‖f‖) ∧
        (∀ (ht : Module.finrank ℝ E < 2 * (s + 2)) (f : FourierSobolevSpace E ℂ s)
            (x : E), χ x = 1 →
          (α : ℂ) * sobolevRepresentative ht (R f) x -
            (∑ i, ∑ j, (a i j (p + r • x) : ℂ) *
              fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht (R f) : E → ℂ) y (b j)) x (b i)) -
            (r : ℂ) * ∑ i, (c i (p + r • x) : ℂ) *
              fderiv ℝ (sobolevRepresentative ht (R f) : E → ℂ) x (b i) =
          sobolevRepresentative hs f x) := by
  let A : Matrix ι ι ℝ := fun i j => a i j p
  let L := physicalQuadraticEquiv b A hA
  let P := rescaledDifferentialPerturbation b a c ha hc χ hχ hχc p hs
  have hev := eventually_localEllipticInverse_small L s P
    (rescaledDifferentialPerturbation_tendsto b a c ha hc χ hχ hχc p hs)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun r hr α hα => ?_⟩
  have hP : anisotropicConstant L * ‖P r‖ ≤ 1 / 2 := he (by simpa [Real.dist_eq] using hr)
  let R := localEllipticInverse L s α hα (P r) hP
  refine ⟨R, norm_localEllipticInverse_le _ _ _ _ _ _,
    fun f => localEllipticInverse_half_bound _ _ _ _ _ _ f, ?_⟩
  intro ht f x hχx
  have hh := congrArg (fun u : FourierSobolevSpace E ℂ s => sobolevRepresentative hs u x)
    (localEllipticInverse_sobolev_equation b A hA s α hα (P r) hP f)
  rw [map_sub, BoundedContinuousFunction.sub_apply, frozenSobolevOperator_representative b A s α hs ht,
    rescaledDifferentialPerturbation_representative b a c ha hc χ hχ hχc p hs r ht _ x hχx] at hh
  change (α : ℂ) * sobolevRepresentative ht (R f) x -
      (∑ i, ∑ j, (a i j p : ℂ) * _) -
      ((∑ i, ∑ j, ((a i j (p + r • x) : ℂ) - (a i j p : ℂ)) * _) + _) = _ at hh
  simp only [sub_mul, Finset.sum_sub_distrib] at hh
  linear_combination hh




end YauCounterexamples
end

end OAI
