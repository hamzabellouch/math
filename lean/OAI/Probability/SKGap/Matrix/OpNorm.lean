import Mathlib
import OAI.Probability.SKGap.Localization.SymmetricElementaryComm

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mul_symmetricElementary_mul (P Q : Matrix ι ι ℝ) (a b i k : ι) :
    (P*symmetricElementary a b*Q) i k = P i a*Q b k+P i b*Q a k := by
  simp [symmetricElementary,Matrix.mul_add,
    Matrix.mul_apply,Matrix.single_apply,ite_and,add_mul,Finset.sum_add_distrib,ite_mul]

lemma goe_inverse_contraction (K B : Matrix ι ι ℝ) (i : ι) :
    (∑ b, (K*B*symmetricElementary i b*K) b i) =
      (Matrix.trace (K*B))*K i i+∑ b, (K*B) b i*K b i := by
  simp_rw [mul_symmetricElementary_mul]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,Matrix.trace]
  exact add_comm _ _

def opNorm (M : Matrix ι ι ℝ) : ℝ := ‖M.toEuclideanLin.toContinuousLinearMap‖
def colVec (M : Matrix ι ι ℝ) (k : ι) : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => M i k)

lemma colVec_eq (M : Matrix ι ι ℝ) (k : ι) :
    colVec M k = M.toEuclideanLin.toContinuousLinearMap (EuclideanSpace.single k (1:ℝ)) := by
  ext i
  simp [colVec,Matrix.toLpLin_apply]

lemma colVec_norm_le (M : Matrix ι ι ℝ) (k : ι) : ‖colVec M k‖ ≤ opNorm M := by
  rw [colVec_eq]
  simpa only [PiLp.norm_single,norm_one,mul_one,opNorm] using!
    M.toEuclideanLin.toContinuousLinearMap.le_opNorm (EuclideanSpace.single k (1:ℝ))

lemma matrix_entry_le_opNorm (M : Matrix ι ι ℝ) (i k : ι) : |M i k| ≤ opNorm M := by
  have h : |M i k| ≤ ‖colVec M k‖ := by
    simpa only [colVec,Real.norm_eq_abs] using (PiLp.norm_apply_le (colVec M k) i)
  exact h.trans (colVec_norm_le M k)

lemma opNorm_mul (M N : Matrix ι ι ℝ) : opNorm (M*N) ≤ opNorm M*opNorm N := by
  have he : (M*N).toEuclideanLin.toContinuousLinearMap =
      M.toEuclideanLin.toContinuousLinearMap * N.toEuclideanLin.toContinuousLinearMap := by
    ext x i
    exact congrFun (congrArg (fun T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι => (T x).ofLp)
      (Matrix.toLpLin_mul 2 2 2 M N)) i
  exact (congrArg norm he).le.trans (norm_mul_le _ _)

lemma goe_cross_contraction_bound (K B : Matrix ι ι ℝ) (i : ι) :
    |∑ b, (K*B) b i*K b i| ≤ opNorm K*opNorm B*opNorm K := by
  have hh := abs_real_inner_le_norm (colVec (K*B) i) (colVec K i)
  change |∑ b, K b i*(K*B) b i| ≤ _ at hh
  simp_rw [mul_comm (K _ _)] at hh
  apply hh.trans
  calc
    ‖colVec (K*B) i‖*‖colVec K i‖ ≤ opNorm (K*B)*opNorm K :=
      mul_le_mul (colVec_norm_le _ _) (colVec_norm_le _ _) (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (opNorm_mul _ _) (norm_nonneg _)

lemma trace_mul_diagonal (K : Matrix ι ι ℝ) (a : ι → ℝ) :
    Matrix.trace (K*Matrix.diagonal a) = ∑ i, a i*K i i := by
  simp [Matrix.trace,Matrix.mul_diagonal,mul_comm]

theorem goe_inverse_loop_raw {r : ℝ} (hr : 0 ≤ r) (B : Matrix ι ι ℝ) (i : ι)
    {K : Matrix ι ι ℝ → Matrix ι ι ℝ} {L : ℝ≥0} {C D : ℝ}
    {s : Set (MatrixCoordinates ι → ℝ)}
    (hf : ∀ a b, LipschitzWith L (fun g => K (goeMatrix r g) a b))
    (hC : ∀ g a b, ‖K (goeMatrix r g) a b‖ ≤ C)
    (hD : ∀ g b, ‖(K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i‖ ≤ D)
    (hs : MeasurableSet s)
    (hder : ∀ g ∈ s, ∀ b, HasDerivAt
      (fun t : ℝ => K (goeMatrix r g+t • symmetricElementary i b) b i)
      ((K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i) 0) :
    |(∫ g, (goeMatrix r g*K (goeMatrix r g)) i i
        ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) -
      r*(∫ g, Matrix.trace (K (goeMatrix r g)*B)*K (goeMatrix r g) i i+
        ∑ b, (K (goeMatrix r g)*B) b i*K (goeMatrix r g) b i
        ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))| ≤
      (Fintype.card ι:ℝ)*(sqrt (2*r)*(L:ℝ)+r*D)*
        (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real sᶜ := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  let d (b : ι) (g : MatrixCoordinates ι → ℝ) :=
    (K (goeMatrix r g)*B*symmetricElementary i b*K (goeMatrix r g)) b i
  have hK : Continuous (fun g => K (goeMatrix r g)) :=
    continuous_pi (fun a => continuous_pi (fun b => (hf a b).continuous))
  have hd (b : ι) : Continuous (d b) := by
    exact ((hK.mul continuous_const).mul continuous_const |>.mul hK).matrix_elem b i
  have hdint (b : ι) : Integrable (d b) μ :=
    Integrable.mono' (integrable_const D) (hd b).aestronglyMeasurable (ae_of_all _ (fun g => hD g b))
  have hwint (b : ι) : Integrable (fun g => goeMatrix r g i b*K (goeMatrix r g) b i) μ := by
    have he (a : MatrixCoordinates ι) : Integrable (fun g : MatrixCoordinates ι → ℝ => g a) μ :=
      integrable_eval (i := a) IsGaussian.integrable_id
    have hw : Integrable (fun g => goeMatrix r g i b) μ :=
      ((he (.inl (i,b))).add (he (.inl (b,i)))).const_mul _
    simpa only [mul_comm] using hw.bdd_mul (hf b i).continuous.aestronglyMeasurable
      (ae_of_all _ (fun g => hC g b i))
  have hb (b : ι) := goe_IBP_error hr i b (H := fun M => K M b i) (d := d b) (hf b i) (fun g => hC g b i)
    (hd b).measurable (fun g => hD g b) hs (fun g hg => hder g hg b)
  have he : (∫ g, Matrix.trace (K (goeMatrix r g)*B)*K (goeMatrix r g) i i+
        ∑ b, (K (goeMatrix r g)*B) b i*K (goeMatrix r g) b i ∂μ) =
      ∑ b, ∫ g, d b g ∂μ := by
    simp_rw [← goe_inverse_contraction]
    exact integral_finsetSum Finset.univ (fun b _ => hdint b)
  change |(∫ g, (goeMatrix r g*K (goeMatrix r g)) i i ∂μ)-r*(_)| ≤ _
  rw [he]
  simp_rw [Matrix.mul_apply]
  rw [integral_finsetSum Finset.univ (fun b _ => hwint b),Finset.mul_sum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ b, |(∫ g, goeMatrix r g i b*K (goeMatrix r g) b i ∂μ)-r*(∫ g, d b g ∂μ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : ι, (sqrt (2*r)*(L:ℝ)+r*D)*μ.real sᶜ :=
      Finset.sum_le_sum (fun b _ => hb b)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end SKGap

end

end OAI
