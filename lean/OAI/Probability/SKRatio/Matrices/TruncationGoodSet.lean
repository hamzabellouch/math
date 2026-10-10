import Mathlib
import OAI.Probability.SKRatio.Matrices.GoeInverseLoopCentered
import OAI.Probability.SKRatio.Matrices.RealPartCLM

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKRatioGaussian
open Matrix Real MeasureTheory ProbabilityTheory
open SKRatioGaussian.RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def truncationGoodSet (r R lo hi : ℝ) (D C : Matrix ι ι ℝ) : Set (MatrixCoordinates ι → ℝ) :=
  {g | opNorm (goeMatrix r g) < R ∧
    lo < ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(goeMatrix r g-C)*D)) ∧
    -hi < ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(goeMatrix r g-C)*D))}

lemma truncationGoodSet_measurable (r R lo hi : ℝ) (D C : Matrix ι ι ℝ) :
    MeasurableSet (truncationGoodSet r R lo hi D C) := by
  have hg := (goeMatrix_pi_lipschitz (ι := ι) r).continuous
  have hc : Continuous (fun g => liftMatrix (1-D*(goeMatrix r g-C)*D)) := by
    dsimp [liftMatrix]; fun_prop
  exact (measurableSet_lt (continuous_realOpNorm.comp hg).measurable measurable_const).inter
    ((measurableSet_lt measurable_const (ComplexSpectral.continuous_lowerRayleigh.comp hc).measurable).inter
      (measurableSet_lt measurable_const (ComplexSpectral.continuous_lowerRayleigh.comp hc.neg).measurable))

lemma realTruncatedK_lipschitz (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (D C : Matrix ι ι ℝ) (hD : Dᵀ = D) (hC : Cᵀ = C) :
    LipschitzWith (Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C)))
      (realTruncatedK f R hR D C) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simp only [dist_eq_norm]
  exact (realTruncatedK_sub_norm f hR D C M N hD hC).trans
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))

omit [Fintype ι] [DecidableEq ι] in
lemma goeMatrix_transpose (r : ℝ) (g : MatrixCoordinates ι → ℝ) :
    (goeMatrix r g)ᵀ = goeMatrix r g := by
  ext i k
  simp [goeMatrix,add_comm]

omit [Fintype ι] in
lemma symmetricElementary_transpose (i k : ι) :
    (symmetricElementary i k)ᵀ = symmetricElementary i k := by
  simp [symmetricElementary,Matrix.transpose_add,Matrix.transpose_single,add_comm]

lemma realTruncatedK_goe_derivative (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C : Matrix ι ι ℝ) (r : ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (g : MatrixCoordinates ι → ℝ)
    (hg : g ∈ truncationGoodSet r R lo hi D C) (i b : ι) :
    HasDerivAt (fun t : ℝ => realTruncatedK f R hR D C (goeMatrix r g+t • symmetricElementary i b) b i)
      ((realTruncatedK f R hR D C (goeMatrix r g)*(D*D)*symmetricElementary i b*
        realTruncatedK f R hR D C (goeMatrix r g)) b i) 0 := by
  exact matrixEntry_derivative
    (realTruncatedK_derivative f hlo hf hR D C (goeMatrix r g) (symmetricElementary i b)
      hD hC (goeMatrix_transpose r g) (symmetricElementary_transpose i b) hg.1 hg.2.1 hg.2.2) b i

theorem realTruncatedK_first_loop (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (D C : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (i : ι) :
    let K := realTruncatedK f R hR D C
    let c := ComplexMatrix.kBound f R (liftMatrix D) (liftMatrix C)
    let L := Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C))
    let Lπ : ℝ≥0 := L*(⟨sqrt (2*r),sqrt_nonneg _⟩ *
      (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
    let T : ℝ≥0 := (⟨sqrt (Fintype.card ι)*opNorm (D*D),
      mul_nonneg (sqrt_nonneg _) (norm_nonneg _)⟩*L)*⟨sqrt (2*r),sqrt_nonneg _⟩+1
    let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
    |(∫ g, (goeMatrix r g*K (goeMatrix r g)) i i ∂μ)-
      r*(∫ g, Matrix.trace (K (goeMatrix r g)*(D*D)) ∂μ)*(∫ g, K (goeMatrix r g) i i ∂μ)| ≤
      (Fintype.card ι:ℝ)*(sqrt (2*r)*(Lπ:ℝ)+r*(2*c*opNorm (D*D)*c))*
        μ.real (truncationGoodSet r R lo hi D C)ᶜ+
        r*(c*((2*Real.exp (π^2/8))*(T:ℝ))+c*opNorm (D*D)*c) := by
  intro K c L Lπ T μ
  have hK : LipschitzWith L K := realTruncatedK_lipschitz f hR D C hD hC
  have ht : LipschitzWith T (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) =>
      Matrix.trace (K (goeMatrix r g)*(D*D))) := by
    exact ((matrixTrace_mul_lipschitz hK (D*D)).comp (goeMatrix_L2_lipschitz r)).weaken
      (le_add_of_nonneg_right (by norm_num))
  have ht0 : 0 < T := by dsimp [T]; positivity
  exact goe_inverse_loop_centered hr (D*D) i hK
    (fun M => realTruncatedK_opNorm f hR D C M hD hC) ht ht0
    (truncationGoodSet_measurable r R lo hi D C)
    (fun g hg b => realTruncatedK_goe_derivative f hlo hf hR D C r hD hC g hg i b)

end SKRatioGaussian

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
