import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.UniformInterior

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

section
omit [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] in
lemma parameter_derivative_smooth (f : P → 𝓢(E,ℂ))
    (hf : ContDiff ℝ ∞ (fun p : P × E => f p.1 p.2)) (v : E) :
    ContDiff ℝ ∞ (fun p : P × E => (∂_{v} (f p.1) : 𝓢(E,ℂ)) p.2) := by
  have hf' : ContDiff ℝ ∞ (fun p : (P × E) × E => f p.1.1 p.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hf'.fderiv_apply (𝕜 := ℝ)
    (f := fun q : P × E => fun x : E => f q.1 x) (g := fun p : P × E => p.2)
    (k := fun _ : P × E => v) contDiff_snd contDiff_const (show (∞ : WithTop ℕ∞)+1 ≤ (∞ : WithTop ℕ∞) by simp)
  simpa only [Function.uncurry, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hd

lemma parameter_coefficientSize_continuous_family (n : ℕ) (f : P → 𝓢(E,ℂ))
    {K : Set E} (hK : IsCompact K) (hs : ∀ t, tsupport (f t) ⊆ K)
    (hf : ContDiff ℝ ∞ (fun p : P × E => f p.1 p.2)) :
    Continuous (fun t => coefficientSize n (f t)) := by
  induction n generalizing f with
  | zero =>
    apply (continuous_bounded_family (fun t => (f t).toBoundedContinuousFunction)
      hK hf.continuous (fun t => (subset_tsupport _).trans (hs t))).norm
  | succ n ih =>
    apply (ih f hs hf).add
    apply continuous_finsetSum
    intro i _
    exact ih (fun t => ∂_{stdOrthonormalBasis ℝ E i} (f t))
      (fun t => (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans (hs t))
      (parameter_derivative_smooth f hf _)

def movingFrozenCoefficient (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p₀ : E) (t : ℝ × E) : 𝓢(E,ℂ) :=
  (hχ.mul_right (f' := fun x => f (t.2 + t.1 • x) - f p₀)).toSchwartzMap
    ((χ.smooth ⊤).mul ((hf.comp (contDiff_const.add (contDiff_const.smul contDiff_id))).sub
      contDiff_const))

omit [FiniteDimensional ℝ E] in
lemma movingFrozenCoefficient_apply (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p₀ : E) (t : ℝ × E) (x : E) :
    movingFrozenCoefficient χ hχ f hf p₀ t x = χ x * (f (t.2+t.1•x)-f p₀) := rfl

lemma movingFrozenCoefficient_size_continuous (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p₀ : E) :
    Continuous (fun t => coefficientSize n (movingFrozenCoefficient χ hχ f hf p₀ t)) := by
  apply parameter_coefficientSize_continuous_family n _ hχ
    (fun _ => tsupport_mul_subset_left)
  change ContDiff ℝ ∞ (fun q : (ℝ × E) × E =>
    χ q.2 * (f (q.1.2+q.1.1•q.2)-f p₀))
  exact ((χ.smooth ⊤).comp contDiff_snd).mul
    ((hf.comp (contDiff_fst.snd.add (contDiff_fst.fst.smul contDiff_snd))).sub contDiff_const)

omit [FiniteDimensional ℝ E] in
lemma movingFrozenCoefficient_zero (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p₀ : E) :
    movingFrozenCoefficient χ hχ f hf p₀ (0,p₀) = 0 := by
  ext x
  simp [movingFrozenCoefficient_apply]

lemma movingFrozenCoefficient_size_tendsto_zero (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p₀ : E) :
    Tendsto (fun t => coefficientSize n (movingFrozenCoefficient χ hχ f hf p₀ t))
      (𝓝 (0,p₀)) (𝓝 0) := by
  have hh := (movingFrozenCoefficient_size_continuous n χ hχ f hf p₀).continuousAt (x := (0,p₀))
  simpa only [ContinuousAt,movingFrozenCoefficient_zero,coefficientSize_zero] using hh

lemma moving_scaledCoefficient_size_continuous (n k : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    Continuous (fun t : ℝ × E => coefficientSize n (scaledCoefficient k χ hχ f hf t.2 t.1)) := by
  apply parameter_coefficientSize_continuous_family n _ hχ
    (fun _ => tsupport_mul_subset_left)
  change ContDiff ℝ ∞ (fun q : (ℝ × E) × E =>
    χ q.2 * ((q.1.1:ℂ)^k * f (q.1.2+q.1.1•q.2)))
  exact ((χ.smooth ⊤).comp contDiff_snd).mul
    (((Complex.ofRealCLM.contDiff.comp contDiff_fst.fst).pow k).mul
      (hf.comp (contDiff_fst.snd.add (contDiff_fst.fst.smul contDiff_snd))))
end

def movingFrozenPrincipal (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p₀ : E) (t : ℝ × E) :
    basisIndex E → basisIndex E → 𝓢(E,ℂ) :=
  fun i j => movingFrozenCoefficient χ hχ (a i j) (ha i j) p₀ t

lemma moving_frozen_principal_size_tendsto (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p₀ : E) :
    Tendsto (fun t => principalCoefficientSize (F := F) n (movingFrozenPrincipal χ hχ a ha p₀ t))
      (𝓝 (0,p₀)) (𝓝 0) := by
  unfold principalCoefficientSize movingFrozenPrincipal
  have hh := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      (movingFrozenCoefficient_size_tendsto_zero n χ hχ (a i j) (ha i j) p₀).mul_const
        ‖secondDerivative (F := F) (n:ℝ) (stdOrthonormalBasis ℝ E i)
          (stdOrthonormalBasis ℝ E j)‖))
  simpa only [zero_mul,Finset.sum_const_zero] using hh

theorem moving_frozen_perturbation_norm_tendsto (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p₀ : E) :
    Tendsto (fun t => ‖perturbation (F := F) n (movingFrozenPrincipal χ hχ a ha p₀ t)‖)
      (𝓝 (0,p₀)) (𝓝 0) := by
  obtain ⟨C,_,hC⟩ := product_operator_estimate (E := E) (F := F) n
  apply squeeze_zero (fun _ => norm_nonneg _) (fun t => perturbation_norm_le n hC _)
  simpa only [mul_zero] using (moving_frozen_principal_size_tendsto (F := F) n χ hχ a ha p₀).const_mul C

end TamingCompatibility.HilbertSobolev

end

end OAI
