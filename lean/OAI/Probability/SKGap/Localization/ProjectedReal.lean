import Mathlib
import OAI.Probability.SKGap.Localization.IntegralAbsSet
import OAI.Probability.SKGap.Brownian.PathBiasBase
import OAI.Probability.SKGap.Localization.Conjugation

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma signConjugate_mul (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M N : Matrix ι ι ℝ) :
    signConjugate s (M*N) = signConjugate s M*signConjugate s N := by
  ext i k
  change s i*s k*(∑ b, M i b*N b k) = ∑ b, (s i*s b*M i b)*(s b*s k*N b k)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = (s i*s k*(M i b*N b k))*1 := by ring
    _ = (s i*s k*(M i b*N b k))*(s b)^2 := by rw [hs b]
    _ = _ := by ring

noncomputable def realProject (R : ℝ) (hR : 0 ≤ R) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  RealComplex.realPart (ComplexMatrix.matrixProject R hR (liftMatrix M))

lemma realProject_opNorm {R : ℝ} (hR : 0 ≤ R) (M : Matrix ι ι ℝ) :
    opNorm (realProject R hR M) ≤ R :=
  (operator_realPart_le _).trans (ComplexMatrix.matrixProject_bound R hR (liftMatrix M)).2

lemma realProject_sub_norm {R : ℝ} (hR : 0 ≤ R) (M N : Matrix ι ι ℝ) :
    ‖realProject R hR M-realProject R hR N‖ ≤ ‖M-N‖ := by
  unfold realProject
  rw [← realPart_sub]
  apply (norm_realPart_le _).trans
  simpa only [← liftMatrix_sub,norm_liftMatrix] using
    ComplexMatrix.matrixProject_sub_norm R hR (liftMatrix M) (liftMatrix N)

lemma realProject_eq_self {R : ℝ} (hR : 0 ≤ R) (M : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hMR : opNorm M ≤ R) : realProject R hR M=M := by
  unfold realProject
  rw [ComplexMatrix.matrixProject_eq_self R hR (liftMatrix M) (liftMatrix_hermitian M hM)
    (by simpa only [ComplexMatrix.opNorm,ComplexMatrix.lin,operator_norm_lift] using hMR)]
  ext i k
  simp [RealComplex.realPart,liftMatrix]

lemma realProject_sign {R : ℝ} (hR : 0 ≤ R) (s : ι → ℝ) (hs : ∀ i, s i^2=1)
    (M : Matrix ι ι ℝ) : realProject R hR (signConjugate s M) = signConjugate s (realProject R hR M) := by
  unfold realProject
  rw [← sign_conjugate_lift s hs M,ComplexMatrix.matrixProject_conjugate,realPart_sign_conjugate]

lemma realProject_lipschitz {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 1 (realProject (ι := ι) R hR) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using realProject_sub_norm hR M N

lemma realProjectedProduct_opNorm {R B : ℝ} (hR : 0 ≤ R)
    (K : Matrix ι ι ℝ → Matrix ι ι ℝ) (hK : ∀ M, opNorm (K M) ≤ B) (M : Matrix ι ι ℝ) :
    opNorm (realProject R hR M*K M) ≤ R*B := by
  apply (opNorm_mul _ _).trans
  exact mul_le_mul (realProject_opNorm hR M) (hK M) (norm_nonneg _) hR

lemma realProjectedProduct_sub_norm {R B L : ℝ} (hR : 0 ≤ R)
    (K : Matrix ι ι ℝ → Matrix ι ι ℝ) (hK : ∀ M, opNorm (K M) ≤ B)
    (hLip : ∀ M N, ‖K M-K N‖ ≤ L*‖M-N‖) (M N : Matrix ι ι ℝ) :
    ‖realProject R hR M*K M-realProject R hR N*K N‖ ≤ (B+R*L)*‖M-N‖ := by
  have he : realProject R hR M*K M-realProject R hR N*K N =
      (realProject R hR M-realProject R hR N)*K M+realProject R hR N*(K M-K N) := by noncomm_ring
  rw [he]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ‖realProject R hR M-realProject R hR N‖*opNorm (K M)+
        opNorm (realProject R hR N)*‖K M-K N‖ :=
      add_le_add (frobenius_mul_le_opNorm_right _ _) (frobenius_mul_le_opNorm _ _)
    _ ≤ ‖M-N‖*B+R*(L*‖M-N‖) := by
      apply add_le_add
      · exact mul_le_mul (realProject_sub_norm hR M N) (hK M) (norm_nonneg _) (norm_nonneg _)
      · exact mul_le_mul (realProject_opNorm hR N) (hLip M N) (norm_nonneg _) hR
    _ = _ := by ring
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma projected_product_expectation_error {R r B : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hB : 0 ≤ B) (K : Matrix ι ι ℝ → Matrix ι ι ℝ) (hK : Continuous K)
    (hKB : ∀ M, opNorm (K M) ≤ B) {s : Set (MatrixCoordinates ι → ℝ)}
    (hs : MeasurableSet s) (hgood : ∀ g ∈ s, opNorm (goeMatrix r g) ≤ R) (i : ι) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
    |(∫ g, (realProject R hR (goeMatrix r g)*K (goeMatrix r g)) i i ∂μ)-
      (∫ g, (goeMatrix r g*K (goeMatrix r g)) i i ∂μ)| ≤
      R*B*μ.real sᶜ+B*(Fintype.card ι:ℝ)*sqrt (2*r)*sqrt (μ.real sᶜ) := by
  intro μ
  let KG := fun g : MatrixCoordinates ι → ℝ => K (goeMatrix r g)
  have hKG : Continuous KG := hK.comp (goeMatrix_pi_lipschitz r).continuous
  have hKe (g : MatrixCoordinates ι → ℝ) (a b : ι) : |KG g a b| ≤ B :=
    (matrix_entry_le_opNorm _ a b).trans (hKB _)
  have hP : Continuous (fun g : MatrixCoordinates ι → ℝ => realProject R hR (goeMatrix r g)*KG g) :=
    ((realProject_lipschitz hR).continuous.comp (goeMatrix_pi_lipschitz r).continuous).matrix_mul hKG
  have hPe (g : MatrixCoordinates ι → ℝ) :
      |(realProject R hR (goeMatrix r g)*KG g) i i| ≤ R*B :=
    (matrix_entry_le_opNorm _ i i).trans (realProjectedProduct_opNorm hR K hKB _)
  have hPI : Integrable (fun g => (realProject R hR (goeMatrix r g)*KG g) i i) μ :=
    Integrable.mono' (integrable_const (R*B)) (hP.matrix_elem i i).aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hPe g))
  have hW (b : ι) : Integrable (fun g => goeMatrix r g i b) μ :=
    (goeEntry_memLp r i b).integrable (by norm_num)
  have hWi (b : ι) : Integrable (fun g => goeMatrix r g i b*KG g b i) μ := by
    simpa only [mul_comm] using (hW b).bdd_mul (hKG.matrix_elem b i).aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hKe g b i))
  have hWI : Integrable (fun g => (goeMatrix r g*KG g) i i) μ :=
    integrable_finsetSum _ (fun b _ => hWi b)
  have hHA : Integrable (fun g => ∑ b, |goeMatrix r g i b|) μ :=
    integrable_finsetSum _ (fun b _ => (hW b).norm)
  let H := fun g => R*B+B*∑ b, |goeMatrix r g i b|
  have hHI : Integrable H μ := (integrable_const _).add (hHA.const_mul B)
  have hb (g : MatrixCoordinates ι → ℝ) :
      ‖(realProject R hR (goeMatrix r g)*KG g) i i-(goeMatrix r g*KG g) i i‖ ≤ H g := by
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add (hPe g) (abs_mul_entry_bound _ _ B (hKe g) i))
  have hraw := integral_exceptional_equal_bound hs.compl hPI hWI hHI
    (fun g hg => by rw [realProject_eq_self hR _ (goeMatrix_transpose r g) (hgood g (by simpa using hg))])
    (fun g _ => hb g)
  have hbad (b : ι) : (∫ g in sᶜ, |goeMatrix r g i b| ∂μ) ≤
      sqrt (2*r)*sqrt (μ.real sᶜ) := by
    apply (integral_abs_on_set_le (goeEntry_memLp r i b) hs.compl).trans
    exact mul_le_mul_of_nonneg_right (sqrt_le_sqrt (goeEntry_integral_sq_le hr i b)) (sqrt_nonneg _)
  apply hraw.trans
  change (∫ g in sᶜ, R*B+B*∑ b, |goeMatrix r g i b| ∂μ) ≤ _
  rw [integral_add (integrable_const _) ((hHA.const_mul B).mono_measure Measure.restrict_le_self),
    integral_const,integral_const_mul]
  have hWa (b : ι) : Integrable (fun g => |goeMatrix r g i b|) (μ.restrict sᶜ) := by
    simpa only [Real.norm_eq_abs] using (hW b).norm.mono_measure Measure.restrict_le_self
  rw [integral_finsetSum _ (fun b _ => hWa b)]
  simp only [measureReal_restrict_apply_univ,smul_eq_mul]
  calc
    _ ≤ μ.real sᶜ*(R*B)+B*(∑ _b : ι, sqrt (2*r)*sqrt (μ.real sᶜ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => hbad b)) hB)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end SKGap
namespace SKGap
open Real

def projectedErrorConstant (j R B rate : ℝ) : ℝ :=
  R*B*(3/rate)+B*sqrt (2*j)*(8*sqrt 3/rate^2)

lemma projected_error_absorption {j R B rate n p : ℝ}
    (hj : 0 ≤ j) (hR : 0 ≤ R) (hB : 0 ≤ B) (hc : 0 < rate)
    (hn : 1 ≤ n) (hp : p ≤ 3*Real.exp (-rate*n)) :
    R*B*p+B*n*sqrt (2*(j/n))*sqrt p ≤ projectedErrorConstant j R B rate/n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hjn : j/n ≤ j := (div_le_iff₀ hn0).mpr (by nlinarith)
  obtain ⟨h₁,_,h₃⟩ := exponential_tail_absorptions hc hn hp
  calc
    _ ≤ R*B*p+B*n*sqrt (2*j)*sqrt p := by gcongr
    _ = R*B*p+B*sqrt (2*j)*(n*sqrt p) := by ring
    _ ≤ R*B*((3/rate)/n)+B*sqrt (2*j)*((8*sqrt 3/rate^2)/n) := by gcongr
    _ = _ := by unfold projectedErrorConstant; ring
end SKGap
end
end

end OAI
