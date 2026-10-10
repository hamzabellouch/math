import OAI.Probability.InvariantIsing.Cavity.CavityGaussianRotation
import Mathlib.Analysis.Matrix.Spectrum

namespace OAI

/-! The Gaussian-pattern Hamiltonian with its diagonal self-interactions.
The array is indexed by spin coordinate first and pattern coordinate second. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

def gaussianPatternArray {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    Matrix (Fin N) (Fin m) ℝ := fun i j => z (i,j)

def gaussianPatternCoupling {N m : ℕ} (c : ℝ) (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    Matrix (Fin N) (Fin N) ℝ :=
  (c/N) • (gaussianPatternArray z * (gaussianPatternArray z)ᵀ)

def gaussianPatternSum {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) (σ : Spin N) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 ((gaussianPatternArray z)ᵀ *ᵥ (fun i => spinValue (σ i)))

def gaussianPatternPressure {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : ℝ :=
  (N : ℝ)⁻¹*logPartition (fun σ : Spin N => c/(2*N)*‖gaussianPatternSum z σ‖^2)

lemma gaussianPatternCoupling_isHermitian {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : (gaussianPatternCoupling c z).IsHermitian := by
  exact (Matrix.isHermitian_mul_conjTranspose_self (gaussianPatternArray z)).smul rfl

lemma quadraticEnergy_dotProduct {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ) (σ : Spin N) :
    quadraticEnergy J σ=(1/2 : ℝ)*
      ((fun i => spinValue (σ i)) ⬝ᵥ J *ᵥ (fun i => spinValue (σ i))) := by
  simp only [quadraticEnergy,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

lemma gaussianPattern_energy {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (σ : Spin N) :
    quadraticEnergy (gaussianPatternCoupling c z) σ=c/(2*N)*‖gaussianPatternSum z σ‖^2 := by
  let v := fun i => spinValue (σ i)
  have hn : ‖gaussianPatternSum z σ‖^2=
      ((gaussianPatternArray z)ᵀ *ᵥ v) ⬝ᵥ ((gaussianPatternArray z)ᵀ *ᵥ v) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [gaussianPatternSum,dotProduct,pow_two]
    rfl
  rw [quadraticEnergy_dotProduct,gaussianPatternCoupling,Matrix.smul_mulVec,dotProduct_smul,
    ← Matrix.mulVec_mulVec,hn]
  rw [Matrix.dotProduct_transpose_mulVec]
  simp only [smul_eq_mul]
  ring

lemma gaussianPatternPressure_eq {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternPressure c z=pressure (gaussianPatternCoupling c z) (fun _ => 0) := by
  simp only [gaussianPatternPressure,pressure,gaussianPattern_energy,fieldEnergy,
    zero_mul,Finset.sum_const_zero,add_zero]

lemma measurable_gaussianPatternPressure (N m : ℕ) (c : ℝ) :
    Measurable (gaussianPatternPressure (N := N) (m := m) c) := by
  unfold gaussianPatternPressure logPartition
  have hm (σ : Spin N) : Measurable (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
      c/(2*N)*‖gaussianPatternSum z σ‖^2) := by
    have hs : Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) => gaussianPatternSum z σ) := by
      unfold gaussianPatternSum gaussianPatternArray
      fun_prop
    exact (hs.measurable.norm.pow_const 2).const_mul _
  exact ((Finset.measurable_sum _ fun σ _ => (hm σ).exp).const_mul _).log.const_mul _

end InvariantIsing

end

end OAI
