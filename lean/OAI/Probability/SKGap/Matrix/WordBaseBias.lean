import Mathlib
import OAI.Probability.SKGap.Gaussian.MatrixWordMoments
import OAI.Probability.SKGap.Matrix.WordPartnerContraction

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma wordDiagonal_nil (i : ι) : wordDiagonal [] i=1 := rfl
omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma wordDiagonal_diag (d : ι→ℝ) (F : List (WordLetter ι)) (i : ι) :
    wordDiagonal (.diag d::F) i=d i*wordDiagonal F i := rfl
omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma wordDiagonal_noise (F : List (WordLetter ι)) (i : ι) :
    wordDiagonal (.noise::F) i=wordDiagonal F i := by simp [wordDiagonal]
omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma wordDiagonal_inverse (F : List (WordLetter ι)) (i : ι) :
    wordDiagonal (.inverse::F) i=wordDiagonal F i := by simp [wordDiagonal]

lemma actualWord_all_diagonal (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (M : Matrix ι ι ℝ)
    (hO : ordinaryCount F=0) (hI : inverseCount F=0) :
    actualWord f R hR j a z F M=diagonal (wordDiagonal F) := by
  induction F with
  | nil =>
    change (1:Matrix ι ι ℝ)=Matrix.diagonal (fun _=>1)
    simp
  | cons l F ih =>
    cases l with
    | noise => simp [ordinaryCount] at hO
    | inverse => simp [inverseCount] at hI
    | diag d =>
      simp only [ordinaryCount,List.countP_cons] at hO
      simp only [inverseCount,List.countP_cons] at hI
      have hh := ih (by simpa [ordinaryCount] using hO) (by simpa [inverseCount] using hI)
      rw [actualWord_cons,hh]
      simp only [WordLetter.eval,Matrix.diagonal_mul_diagonal]
      rfl

lemma actualWord_no_noise_entry (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (M : Matrix ι ι ℝ) (i : ι)
    (hO : ordinaryCount F=0) (hI : inverseCount F≤1) :
    actualWord f R hR j a z F M i i=wordDiagonal F i*
      (if inverseCount F=0 then 1 else pathK f R hR j a z M i i) := by
  induction F with
  | nil => simp [actualWord_nil,inverseCount]
  | cons l F ih =>
    cases l with
    | noise => simp [ordinaryCount] at hO
    | diag d =>
      have hOt : ordinaryCount F=0 := by simpa [ordinaryCount] using hO
      have hIt : inverseCount F≤1 := by simpa [inverseCount] using hI
      rw [actualWord_cons]
      simp only [WordLetter.eval,Matrix.diagonal_mul,ih hOt hIt,wordDiagonal_diag]
      have he : inverseCount (.diag d::F)=inverseCount F := by simp [inverseCount]
      rw [he]
      ring
    | inverse =>
      have hOt : ordinaryCount F=0 := by simpa [ordinaryCount] using hO
      have hIt : inverseCount F=0 := by simp [inverseCount] at hI ⊢;omega
      rw [actualWord_cons,actualWord_all_diagonal f hR j a z F M hOt hIt]
      simp only [WordLetter.eval,Matrix.mul_diagonal,wordDiagonal_inverse]
      have hh : inverseCount (.inverse::F)≠0 := by simp [inverseCount]
      rw [ite_eq_right hh,mul_comm]

omit [Fintype ι] [DecidableEq ι] in
lemma wordDiagonal_bound (D : ℝ) (hD : 1≤D) (F : List (WordLetter ι))
    (hF : ∀ l∈F,l.bounded D) (i : ι) : |wordDiagonal F i|≤D^F.length := by
  induction F with
  | nil => simp
  | cons l F ih =>
    have hFt : ∀ l∈F,l.bounded D := fun l hl=>hF l (List.mem_cons_of_mem _ hl)
    have hD0 : 0≤D := zero_le_one.trans hD
    cases l with
    | diag d =>
      rw [wordDiagonal_diag,abs_mul]
      simpa only [List.length_cons,pow_succ'] using mul_le_mul (hF (.diag d) List.mem_cons_self i)
        (ih hFt) (abs_nonneg _) hD0
    | noise =>
      simp only [wordDiagonal_noise,List.length_cons]
      exact (ih hFt).trans (pow_le_pow_right₀ hD (Nat.le_succ _))
    | inverse =>
      simp only [wordDiagonal_inverse,List.length_cons]
      exact (ih hFt).trans (pow_le_pow_right₀ hD (Nat.le_succ _))

def wordExpected (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (i : ι) : ℝ :=
  ∫ g : MatrixCoordinates ι→ℝ,actualWord f R hR j a z F (goeMatrix (j/(Fintype.card ι:ℝ)) g) i i
    ∂Measure.pi (fun _=>gaussianReal 0 1)

theorem word_base_bias (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (i : ι)
    (hO : ordinaryCount F=0) (hI : inverseCount F≤1) {D E : ℝ}
    (hD : 1≤D) (hF : ∀ l∈F,l.bounded D) (hE : 0≤E)
    (hb : |pathExpected f R hR j a z i-1|≤E) :
    |wordExpected f hR j a z F i-wordDiagonal F i|≤D^F.length*E := by
  have he (g : MatrixCoordinates ι→ℝ) := actualWord_no_noise_entry f hR j a z F
    (goeMatrix (j/(Fintype.card ι:ℝ)) g) i hO hI
  by_cases hIc : inverseCount F=0
  · have hh : wordExpected f hR j a z F i=wordDiagonal F i := by simp [wordExpected,he,hIc]
    rw [hh,sub_self,abs_zero]
    positivity
  · have hh : wordExpected f hR j a z F i=wordDiagonal F i*pathExpected f R hR j a z i := by
      simp only [wordExpected,he,ite_eq_right hIc,integral_const_mul,pathExpected,pathK,expectedCutoff]
    rw [hh,← mul_sub_one,abs_mul]
    exact mul_le_mul (wordDiagonal_bound D hD F hF i) hb (abs_nonneg _) (pow_nonneg (zero_le_one.trans hD) _)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma matrix_word_expectation_contraction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0<n)
    (U V Q : Ω→Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    {j BU BQ BV T : ℝ} (hj : 0≤j) (hBU : 0≤BU) (_hBQ : 0≤BQ) (hBV : 0≤BV)
    (hU : ∀ ω,opNorm (U ω) ≤ BU) (hQ : ∀ ω,opNorm (Q ω) ≤ BQ)
    (hV : ∀ ω,opNorm (V ω) ≤ BV)
    (hY : AEStronglyMeasurable (fun ω=>(U ω*Q ω) i i) μ)
    (hZ : AEStronglyMeasurable (fun ω=>(U ω*(V ω)ᵀ*Q ω) i i) μ)
    (hX : Integrable (fun ω=>trace (V ω)/(n:ℝ)) μ)
    (hT : (∫ ω,|trace (V ω)/(n:ℝ)-∫ v,trace (V v)/(n:ℝ) ∂μ| ∂μ) ≤ T) :
    |(j/(n:ℝ))*(∫ ω,∑ a,∑ b,U ω i a*(V ω*symmetricElementary a b*Q ω) b i ∂μ)-
      j*(∫ ω,trace (V ω)/(n:ℝ) ∂μ)*(∫ ω,(U ω*Q ω) i i ∂μ)| ≤
      j*(BU*BQ*T+BU*BV*BQ/(n:ℝ)) := by
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hYb : ∀ ω,‖(U ω*Q ω) i i‖ ≤ BU*BQ := by
    intro ω
    exact (matrix_entry_le_opNorm _ i i).trans ((opNorm_mul _ _).trans
      (mul_le_mul (hU ω) (hQ ω) (norm_nonneg _) hBU))
  have hZb : ∀ ω,‖(U ω*(V ω)ᵀ*Q ω) i i/(n:ℝ)‖ ≤ BU*BV*BQ/(n:ℝ) := by
    intro ω
    rw [norm_div,Real.norm_of_nonneg hnr.le]
    apply div_le_div_of_nonneg_right _ hnr.le
    exact (matrix_word_reverse_bound (U ω) (V ω) (Q ω) i).trans
      (mul_le_mul (mul_le_mul (hU ω) (hV ω) (norm_nonneg _) hBU) (hQ ω) (norm_nonneg _) (mul_nonneg hBU hBV))
  have hZi : Integrable (fun ω=>(U ω*(V ω)ᵀ*Q ω) i i/(n:ℝ)) μ :=
    (integrable_const (BU*BV*BQ/(n:ℝ))).mono' (by simpa only [div_eq_mul_inv,Pi.mul_apply] using! hZ.mul (g := fun _ => (n:ℝ)⁻¹) aestronglyMeasurable_const) (ae_of_all _ hZb)
  have he : (∫ ω,(j/(n:ℝ))*(∑ a,∑ b,U ω i a*(V ω*symmetricElementary a b*Q ω) b i) ∂μ) =
      j*(∫ ω,(trace (V ω)/(n:ℝ))*((U ω*Q ω) i i)+(U ω*(V ω)ᵀ*Q ω) i i/(n:ℝ) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [matrix_word_contraction]
    ring
  have hh := integral_loop_deviation (μ:=μ) hj hX hY (ae_of_all _ hYb)
    hZi (ae_of_all _ hZb) hT
    (V:=fun ω=>(j/(n:ℝ))*(∑ a,∑ b,U ω i a*(V ω*symmetricElementary a b*Q ω) b i))
    (E:=0) (by rw [he,sub_self,abs_zero])
  simpa only [integral_const_mul,zero_add] using hh

theorem goe_word_leading_contraction {n : ℕ} (hn : 0<n) {j : ℝ} (hj : 0<j)
    (F : List (Matrix (Fin n) (Fin n) ℝ→Matrix (Fin n) (Fin n) ℝ))
    {R : NNReal} (hR : 0<R)
    (hF : ∀ f∈F,∀ M,opNorm (f M) ≤ R) (hL : ∀ f∈F,LipschitzWith R f)
    (U Q : Matrix (Fin n) (Fin n) ℝ→Matrix (Fin n) (Fin n) ℝ)
    (hUc : Continuous U) (hQc : Continuous Q) {BU BQ : ℝ} (hBU : 0≤BU) (hBQ : 0≤BQ)
    (hU : ∀ M,opNorm (U M) ≤ BU) (hQ : ∀ M,opNorm (Q M) ≤ BQ) (i : Fin n) :
    let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)
    let W := goeMatrix (j/n)
    |(j/(n:ℝ))*(∫ g,∑ a,∑ b,U (W g) i a*
      (matrixFactorProduct F (W g)*symmetricElementary a b*Q (W g)) b i ∂μ)-
      j*(∫ g,trace (matrixFactorProduct F (W g))/(n:ℝ) ∂μ)*(∫ g,(U (W g)*Q (W g)) i i ∂μ)| ≤
      (j*(BU*BQ*((2*exp (π^2/8))*((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j))+
        BU*(R:ℝ)^F.length*BQ))/(n:ℝ) := by
  dsimp only
  have hG := (goeMatrix_pi_lipschitz (ι:=Fin n) (j/n)).continuous
  have hW := (matrixFactorProduct_lipschitz F hF hL).continuous.comp hG
  have hUc' := hUc.comp hG
  have hQc' := hQc.comp hG
  have hY : Continuous (fun g : MatrixCoordinates (Fin n)→ℝ=>(U (goeMatrix (j/n) g)*Q (goeMatrix (j/n) g)) i i) := by
    exact (continuous_apply i).comp ((continuous_apply i).comp (hUc'.mul hQc'))
  have hZ : Continuous (fun g : MatrixCoordinates (Fin n)→ℝ=>
      (U (goeMatrix (j/n) g)*(matrixFactorProduct F (goeMatrix (j/n) g))ᵀ*Q (goeMatrix (j/n) g)) i i) := by
    exact (continuous_apply i).comp ((continuous_apply i).comp ((hUc'.mul hW.matrix_transpose).mul hQc'))
  have hh := matrix_word_expectation_contraction
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)) hn
    (fun g=>U (goeMatrix (j/n) g)) (fun g=>matrixFactorProduct F (goeMatrix (j/n) g))
    (fun g=>Q (goeMatrix (j/n) g)) i hj.le hBU hBQ (pow_nonneg R.coe_nonneg _)
    (fun g=>hU _) (fun g=>hQ _) (fun g=>matrixFactorProduct_opNorm F hF _)
    hY.aestronglyMeasurable hZ.aestronglyMeasurable
    (gaussianProduct_integrable_lipschitz (goe_word_trace_lip_scaled hn hj.le F hF hL))
    (goe_word_trace_centered_L1_all hn hj F hR hF hL)
  apply hh.trans_eq
  ring
end SKGap
end
end

end OAI
