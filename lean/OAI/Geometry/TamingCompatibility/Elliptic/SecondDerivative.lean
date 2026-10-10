import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Product
import OAI.Geometry.TamingCompatibility.Elliptic.NeumannSeries

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def secondDerivative (s : ℝ) (v w : E) : H E F (s+2) →L[ℂ] H E F s :=
  (derivative (s+1) v).comp (derivative (s+2) w)

lemma toDistribution_secondDerivative (s : ℝ) (v w : E) (u : H E F (s+2)) :
    toDistribution E F s (secondDerivative s v w u) =
      ∂_{v} (∂_{w} (toDistribution E F (s+2) u)) := by
  have h1 := toDistribution_derivative (s+1) v (derivative (s+2) w u)
  have e1 : s+1-1=s := by ring
  rw [e1] at h1
  have h2 := toDistribution_derivative (s+2) w u
  have e2 : s+2-1=s+1 := by ring
  rw [e2] at h2
  exact h1.trans (congrArg (fun t : 𝓢'(E,F) => ∂_{v} t) h2)

def differentialPerturbation
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  ∑ i, ∑ j, smulLeftCLM F (a i j)
    (∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j} u))

def perturbation (n : ℕ) (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) :
    H E F ((n:ℝ)+2) →L[ℂ] H E F n :=
  ∑ i, ∑ j, (product n (a i j)).comp
    (secondDerivative n (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j))

lemma toDistribution_perturbation (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (u : H E F ((n:ℝ)+2)) :
    toDistribution E F n (perturbation n a u) =
      differentialPerturbation a (toDistribution E F ((n:ℝ)+2) u) := by
  simp only [perturbation, differentialPerturbation, sum_apply,
    ContinuousLinearMap.comp_apply, map_sum, toDistribution_product,
    toDistribution_secondDerivative]

def principalCoefficientSize (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) : ℝ :=
  ∑ i, ∑ j, coefficientSize n (a i j) *
    ‖secondDerivative (F := F) n (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)‖

lemma principalCoefficientSize_nonneg (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) :
    0 ≤ principalCoefficientSize (F := F) n a := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (coefficientSize_nonneg _ _) (norm_nonneg _)))

lemma perturbation_norm_le (n : ℕ) {C : ℝ}
    (hp : ∀ g : 𝓢(E,ℂ), ‖product (F := F) n g‖ ≤ C * coefficientSize n g)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) :
    ‖perturbation (F := F) n a‖ ≤ C * principalCoefficientSize (F := F) n a := by
  unfold perturbation principalCoefficientSize
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right (hp (a i j))
          (norm_nonneg (secondDerivative (F := F) n
            (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)))))

def perturbedHelmholtz (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  EuclideanGreen.helmholtz u + differentialPerturbation a u

lemma helmholtz_toDistribution (s : ℝ) (u : H E F (s+2)) :
    EuclideanGreen.helmholtz (toDistribution E F (s+2) u) = toDistribution E F s u := by
  have h := toDistribution_reindex (s+2) s u
  have he : s+2-s=2 := by ring
  rw [he, EuclideanGreen.bessel_two_eq_helmholtz] at h
  exact h.symm

lemma perturbedHelmholtz_toDistribution (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (u : H E F ((n:ℝ)+2)) :
    perturbedHelmholtz a (toDistribution E F ((n:ℝ)+2) u) =
      toDistribution E F n (u + perturbation n a u) := by
  rw [perturbedHelmholtz, helmholtz_toDistribution, map_add, toDistribution_perturbation]

theorem perturbedHelmholtz_solve (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ‖perturbation (F := F) n a‖ < 1) {f : 𝓢'(E,F)}
    (hf : MemSobolev n 2 f) :
    ∃! u : 𝓢'(E,F), MemSobolev ((n:ℝ)+2) 2 u ∧ perturbedHelmholtz a u = f := by
  have hf' : f ∈ Set.range (toDistribution E F n) := by
    rw [range_toDistribution]
    exact hf
  obtain ⟨v, hv⟩ := hf'
  obtain ⟨w, hw, hu⟩ := Neumann.existsUnique (perturbation (F := F) n a) ha v
  refine ⟨toDistribution E F ((n:ℝ)+2) w,
    ⟨toDistribution_memSobolev _ _, ?_⟩, ?_⟩
  · rw [perturbedHelmholtz_toDistribution, hw, hv]
  · intro z hz
    have hz' : z ∈ Set.range (toDistribution E F ((n:ℝ)+2)) := by
      rw [range_toDistribution]
      exact hz.1
    obtain ⟨q, hq⟩ := hz'
    have he : q + perturbation n a q = v := by
      apply toDistribution_injective (n:ℝ)
      rw [← perturbedHelmholtz_toDistribution, hq, hz.2, hv]
    rw [← hq, hu q he]

theorem exists_principal_perturbation_threshold (n : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : basisIndex E → basisIndex E → 𝓢(E,ℂ),
      principalCoefficientSize (F := F) n a < ε →
      ∀ f : 𝓢'(E,F), MemSobolev n 2 f →
        ∃! u : 𝓢'(E,F), MemSobolev ((n:ℝ)+2) 2 u ∧ perturbedHelmholtz a u = f := by
  obtain ⟨C, hC, hp⟩ := product_operator_estimate (E := E) (F := F) n
  refine ⟨C⁻¹, inv_pos.mpr hC, fun a ha f hf => ?_⟩
  apply perturbedHelmholtz_solve n a _ hf
  have h := mul_lt_mul_of_pos_left ha hC
  rw [mul_inv_cancel₀ hC.ne'] at h
  exact (perturbation_norm_le n hp a).trans_lt h

end TamingCompatibility.HilbertSobolev

end

end OAI
