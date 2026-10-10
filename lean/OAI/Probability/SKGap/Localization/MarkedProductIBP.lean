import Mathlib
import OAI.Probability.SKGap.Matrix.MarkedWordIBP

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

lemma scalar_bounded_product_lipschitz {X : Type*} [PseudoMetricSpace X]
    {u v : X→ℝ} {L K B C : NNReal} (hu : LipschitzWith L u) (hv : LipschitzWith K v)
    (hB : ∀ x,‖u x‖≤B) (hC : ∀ x,‖v x‖≤C) :
    LipschitzWith (L*C+B*K) (fun x=>u x*v x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have he : u x*v x-u y*v y=(u x-u y)*v x+u y*(v x-v y) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  have hut := hu.dist_le_mul x y
  have hvt := hv.dist_le_mul x y
  rw [dist_eq_norm] at hut hvt
  have hh := mul_le_mul hut (hC x) (norm_nonneg _) (mul_nonneg L.coe_nonneg dist_nonneg)
  have hh' := mul_le_mul (hB y) hvt (norm_nonneg _) B.coe_nonneg
  apply (add_le_add hh hh').trans_eq
  simp only [NNReal.coe_add,NNReal.coe_mul]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem goe_marked_product_IBP {r : ℝ} (hr : 0≤r)
    (U Q : Matrix ι ι ℝ→Matrix ι ι ℝ)
    (DU DQ : ι→ι→Matrix ι ι ℝ→Matrix ι ι ℝ)
    {L K B C : NNReal} {D E : ℝ}
    (hU : LipschitzWith L U) (hQ : LipschitzWith K Q)
    (hB : ∀ M,opNorm (U M)≤B) (hC : ∀ M,opNorm (Q M)≤C)
    (hDU : ∀ a b,Continuous (DU a b)) (hDQ : ∀ a b,Continuous (DQ a b))
    (hD : ∀ a b M,opNorm (DU a b M)≤D) (hE : ∀ a b M,opNorm (DQ a b M)≤E)
    {s : Set (MatrixCoordinates ι→ℝ)} (hs : MeasurableSet s)
    (hUd : ∀ a b g,g∈s→HasDerivAt (fun t : ℝ=>U (goeMatrix r g+t • symmetricElementary a b)) (DU a b (goeMatrix r g)) 0)
    (hQd : ∀ a b g,g∈s→HasDerivAt (fun t : ℝ=>Q (goeMatrix r g+t • symmetricElementary a b)) (DQ a b (goeMatrix r g)) 0)
    (i : ι) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1)
    |(∫ g,(U (goeMatrix r g)*goeMatrix r g*Q (goeMatrix r g)) i i ∂μ)-
      r*(∫ g,∑ a,∑ b,(DU a b (goeMatrix r g) i a*Q (goeMatrix r g) b i+
        U (goeMatrix r g) i a*DQ a b (goeMatrix r g) b i) ∂μ)|≤
      (Fintype.card ι:ℝ)^2*(sqrt (2*r)*((L*C+B*K:NNReal)*(⟨sqrt (2*r),sqrt_nonneg _⟩*(Fintype.card (MatrixCoordinates ι):NNReal)^(1/(2:ℝ≥0∞)).toReal):NNReal)+
        r*(D*C+B*E))*μ.real sᶜ := by
  intro μ
  let H := fun a b M=>(U M) i a*(Q M) b i
  let d := fun a b g=>(DU a b (goeMatrix r g)) i a*(Q (goeMatrix r g)) b i+
    (U (goeMatrix r g)) i a*(DQ a b (goeMatrix r g)) b i
  have hG := (goeMatrix_pi_lipschitz (ι:=ι) r)
  have hu (a : ι) : LipschitzWith L (fun M=>(U M) i a) := by
    simpa only [one_mul,Function.comp_def] using! (matrixEntry_lipschitz i a).comp hU
  have hq (b : ι) : LipschitzWith K (fun M=>(Q M) b i) := by
    simpa only [one_mul,Function.comp_def] using! (matrixEntry_lipschitz b i).comp hQ
  have hub (M : Matrix ι ι ℝ) (a : ι) : ‖(U M) i a‖≤(B:ℝ) :=
    (matrix_entry_le_opNorm _ i a).trans (hB M)
  have hqb (M : Matrix ι ι ℝ) (b : ι) : ‖(Q M) b i‖≤(C:ℝ) :=
    (matrix_entry_le_opNorm _ b i).trans (hC M)
  have hdh (a b : ι) : Measurable (d a b) := by
    exact (((hDU a b).comp hG.continuous).matrix_elem i a |>.mul ((hQ.continuous.comp hG.continuous).matrix_elem b i) |>.add
      (((hU.continuous.comp hG.continuous).matrix_elem i a).mul (((hDQ a b).comp hG.continuous).matrix_elem b i))).measurable
  have hdb (a b : ι) (g : MatrixCoordinates ι→ℝ) : ‖d a b g‖≤D*C+B*E := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    exact add_le_add (mul_le_mul ((matrix_entry_le_opNorm _ i a).trans (hD a b _)) (hqb _ b) (norm_nonneg _)
      (le_trans (show 0≤opNorm (DU a b (goeMatrix r g)) from norm_nonneg _) (hD a b _)))
      (mul_le_mul (hub _ a) ((matrix_entry_le_opNorm _ b i).trans (hE a b _)) (norm_nonneg _) B.coe_nonneg)
  have hh := goe_marked_sum_IBP hr H d
    (fun a b=>(scalar_bounded_product_lipschitz (hu a) (hq b) (fun M=>hub M a) (fun M=>hqb M b)).comp hG)
    (C:=(B:ℝ)*C) (fun a b g=>by rw [norm_mul];exact mul_le_mul (hub _ a) (hqb _ b) (norm_nonneg _) B.coe_nonneg)
    hdh hdb hs (fun a b g hg=>by
      have ha := matrixEntry_derivative (hUd a b g hg) i a
      have hb := matrixEntry_derivative (hQd a b g hg) b i
      simpa only [H,d,zero_smul,add_zero] using! ha.fun_mul hb)
  simpa only [H,d,← matrix_marked_expand,μ] using! hh
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma marked_entry_bound (U W Q : Matrix ι ι ℝ) {B C : ℝ} (hB : 0≤B) ( _hC : 0≤C)
    (hU : opNorm U≤B) (hQ : opNorm Q≤C) (i : ι) :
    |(U*W*Q) i i|≤B*C*(∑ a,∑ b,|W a b|) := by
  rw [matrix_marked_expand]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [abs_mul,abs_mul]
  have hh := mul_le_mul ((matrix_entry_le_opNorm _ i a).trans hU)
    ((matrix_entry_le_opNorm _ b i).trans hQ) (abs_nonneg _) hB
  nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (W a b))]

theorem projected_marked_expectation_error {r R B C : ℝ} (hr : 0≤r) (hR : 0≤R)
    (hB : 0≤B) (hC : 0≤C) (U Q : Matrix ι ι ℝ→Matrix ι ι ℝ)
    (hU : Continuous U) (hQ : Continuous Q) (hUb : ∀ M,opNorm (U M)≤B) (hQb : ∀ M,opNorm (Q M)≤C)
    {s : Set (MatrixCoordinates ι→ℝ)} (hs : MeasurableSet s)
    (hgood : ∀ g∈s,opNorm (goeMatrix r g)≤R) (i : ι) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1)
    |(∫ g,(U (goeMatrix r g)*realProject R hR (goeMatrix r g)*Q (goeMatrix r g)) i i ∂μ)-
      (∫ g,(U (goeMatrix r g)*goeMatrix r g*Q (goeMatrix r g)) i i ∂μ)|≤
      B*R*C*μ.real sᶜ+B*C*(Fintype.card ι:ℝ)^2*sqrt (2*r)*sqrt (μ.real sᶜ) := by
  intro μ
  let W := goeMatrix (ι:=ι) r
  have hWc := (goeMatrix_pi_lipschitz (ι:=ι) r).continuous
  have hUc := hU.comp hWc
  have hQc := hQ.comp hWc
  have hPc := (realProject_lipschitz hR).continuous.comp hWc
  have hpb (g : MatrixCoordinates ι→ℝ) : ‖(U (W g)*realProject R hR (W g)*Q (W g)) i i‖≤B*R*C := by
    exact (matrix_entry_le_opNorm _ i i).trans ((opNorm_mul _ _).trans
      (mul_le_mul ((opNorm_mul _ _).trans (mul_le_mul (hUb _) (realProject_opNorm hR _) (norm_nonneg _) hB))
        (hQb _) (norm_nonneg _) (mul_nonneg hB hR)))
  have hpi : Integrable (fun g=>(U (W g)*realProject R hR (W g)*Q (W g)) i i) μ :=
    (integrable_const (B*R*C)).mono' (((hUc.matrix_mul hPc).matrix_mul hQc).matrix_elem i i).aestronglyMeasurable (ae_of_all _ hpb)
  have hwa (a b : ι) : Integrable (fun g=>|W g a b|) μ := by
    exact ((goeEntry_memLp r a b).integrable (by norm_num)).norm
  have hwai : Integrable (fun g=>∑ a,∑ b,|W g a b|) μ :=
    integrable_finsetSum _ (fun a _=>integrable_finsetSum _ (fun b _=>hwa a b))
  have hwb (g : MatrixCoordinates ι→ℝ) : ‖(U (W g)*W g*Q (W g)) i i‖≤B*C*(∑ a,∑ b,|W g a b|) :=
    marked_entry_bound _ _ _ hB hC (hUb _) (hQb _) i
  have hwi : Integrable (fun g=>(U (W g)*W g*Q (W g)) i i) μ :=
    (hwai.const_mul (B*C)).mono' (((hUc.matrix_mul hWc).matrix_mul hQc).matrix_elem i i).aestronglyMeasurable (ae_of_all _ hwb)
  have herr := integral_exceptional_equal_bound hs.compl hpi hwi
    ((integrable_const (B*R*C)).add (hwai.const_mul (B*C)))
    (fun g hg=>by rw [realProject_eq_self hR _ (goeMatrix_transpose r g) (hgood g (by simpa using hg))])
    (fun g _=>(norm_sub_le _ _).trans (add_le_add (hpb g) (hwb g)))
  apply herr.trans
  have hwas (a b : ι) : Integrable (fun g=>|W g a b|) (μ.restrict sᶜ) := (hwa a b).mono_measure Measure.restrict_le_self
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const _) ((hwai.const_mul (B*C)).mono_measure Measure.restrict_le_self),integral_const,integral_const_mul]
  rw [integral_finsetSum _ (fun a _=>integrable_finsetSum _ (fun b _=>hwas a b))]
  simp_rw [integral_finsetSum _ (fun b _=>hwas _ b)]
  have hbad (a b : ι) : (∫ g in sᶜ,|W g a b| ∂μ)≤ sqrt (2*r)*sqrt (μ.real sᶜ) :=
    (integral_abs_on_set_le (goeEntry_memLp r a b) hs.compl).trans
      (mul_le_mul_of_nonneg_right (sqrt_le_sqrt (goeEntry_integral_sq_le hr a b)) (sqrt_nonneg _))
  simp only [measureReal_restrict_apply_univ,smul_eq_mul]
  calc
    _ ≤ μ.real sᶜ*(B*R*C)+B*C*(∑ a : ι,∑ b : ι,sqrt (2*r)*sqrt (μ.real sᶜ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hbad a b))) (mul_nonneg hB hC))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
end SKGap
end
end

end OAI
