import Mathlib
import OAI.Probability.SKGap.Matrix.WordDerivative

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma matrix_marked_expand (U W Q : Matrix ι ι ℝ) (i : ι) :
    (U*W*Q) i i=∑ a,∑ b,W a b*(U i a*Q b i) := by
  simp only [Matrix.mul_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _;apply Finset.sum_congr rfl
  intro b _;ring

theorem goe_marked_sum_IBP {r : ℝ} (hr : 0≤r)
    (H : ι→ι→Matrix ι ι ℝ→ℝ) (d : ι→ι→(MatrixCoordinates ι→ℝ)→ℝ)
    {L : NNReal} {C D : ℝ} {s : Set (MatrixCoordinates ι→ℝ)}
    (hL : ∀ a b,LipschitzWith L (fun g=>H a b (goeMatrix r g)))
    (hC : ∀ a b g,‖H a b (goeMatrix r g)‖≤C)
    (hd : ∀ a b,Measurable (d a b)) (hD : ∀ a b g,‖d a b g‖≤D)
    (hs : MeasurableSet s)
    (hder : ∀ a b g,g∈s→HasDerivAt (fun t : ℝ=>H a b (goeMatrix r g+t • symmetricElementary a b)) (d a b g) 0) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1)
    |(∫ g,∑ a,∑ b,goeMatrix r g a b*H a b (goeMatrix r g) ∂μ)-
      r*(∫ g,∑ a,∑ b,d a b g ∂μ)|≤
      (Fintype.card ι:ℝ)^2*(sqrt (2*r)*(L:ℝ)+r*D)*μ.real sᶜ := by
  intro μ
  have hWi (a b : ι) : Integrable (fun g=>goeMatrix r g a b*H a b (goeMatrix r g)) μ := by
    simpa only [mul_comm] using ((goeEntry_memLp r a b).integrable (by norm_num)).bdd_mul
      (hL a b).continuous.aestronglyMeasurable (ae_of_all _ (hC a b))
  have hdi (a b : ι) : Integrable (d a b) μ :=
    (integrable_const D).mono' (hd a b).aestronglyMeasurable (ae_of_all _ (hD a b))
  rw [integral_finsetSum _ (fun a _=>integrable_finsetSum _ (fun b _=>hWi a b)),
    integral_finsetSum _ (fun a _=>integrable_finsetSum _ (fun b _=>hdi a b))]
  simp_rw [integral_finsetSum _ (fun b _=>hWi _ b),integral_finsetSum _ (fun b _=>hdi _ b),
    Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a : ι,∑ b : ι,(sqrt (2*r)*(L:ℝ)+r*D)*μ.real sᶜ := by
      apply Finset.sum_le_sum
      intro a _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun b _=>goe_IBP_error hr a b (hL a b) (hC a b)
        (hd a b) (hD a b) hs (hder a b))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

lemma actualWord_append (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (F G : List (WordLetter ι)) (M : Matrix ι ι ℝ) :
    actualWord f R hR j a z (F++G) M=actualWord f R hR j a z F M*actualWord f R hR j a z G M := by
  simp only [actualWord,matrixFactorProduct,List.map_append,List.prod_append]

lemma actualWordDirection_append (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (F G : List (WordLetter ι)) (M E : Matrix ι ι ℝ) :
    actualWordDirection f R hR j a z M E (F++G)=
      actualWordDirection f R hR j a z M E F*actualWord f R hR j a z G M+
        actualWord f R hR j a z F M*actualWordDirection f R hR j a z M E G := by
  induction F with
  | nil => simp [actualWordDirection,actualWord,matrixFactorProduct]
  | cons l F ih =>
    simp only [List.cons_append,actualWordDirection,actualWord_append,ih]
    change l.direction f R hR j a z M E*(actualWord f R hR j a z F M*actualWord f R hR j a z G M)+
      l.eval f R hR j a z M*(actualWordDirection f R hR j a z M E F*actualWord f R hR j a z G M+
        actualWord f R hR j a z F M*actualWordDirection f R hR j a z M E G)=
      (l.direction f R hR j a z M E*actualWord f R hR j a z F M+
        l.eval f R hR j a z M*actualWordDirection f R hR j a z M E F)*actualWord f R hR j a z G M+
      (l.eval f R hR j a z M*actualWord f R hR j a z F M)*actualWordDirection f R hR j a z M E G
    noncomm_ring
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_word_contraction (U V Q : Matrix ι ι ℝ) (i : ι) :
    (∑ a,∑ b,U i a*(V*symmetricElementary a b*Q) b i) =
      (U*Q) i i*trace V+(U*Vᵀ*Q) i i := by
  simp_rw [mul_symmetricElementary_mul,mul_add]
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ a,∑ b,U i a*(V b a*Q b i))=(U*Vᵀ*Q) i i := by
    simp only [Matrix.mul_apply,transpose_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _;apply Finset.sum_congr rfl
    intro a _;ring
  have h2 : (∑ a,∑ b,U i a*(V b b*Q a i))=(U*Q) i i*trace V := by
    simp only [Matrix.mul_apply,Matrix.trace,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _;apply Finset.sum_congr rfl
    intro b _;dsimp only [Matrix.diag];ring
  rw [h1,h2,add_comm]

lemma matrix_word_reverse_bound (U V Q : Matrix ι ι ℝ) (i : ι) :
    |(U*Vᵀ*Q) i i| ≤ opNorm U*opNorm V*opNorm Q := by
  apply (matrix_entry_le_opNorm (U*Vᵀ*Q) i i).trans
  apply (opNorm_mul (U*Vᵀ) Q).trans
  have hh := mul_le_mul_of_nonneg_right (opNorm_mul U Vᵀ) (show 0 ≤ opNorm Q from norm_nonneg _)
  simpa only [opNorm_transpose] using hh

lemma matrix_word_scaled_contraction (U V Q : Matrix ι ι ℝ) (i : ι) {j : ℝ} (hj : 0 ≤ j) :
    |(j/Fintype.card ι)*(∑ a,∑ b,U i a*(V*symmetricElementary a b*Q) b i)-
      j*(trace V/Fintype.card ι)*(U*Q) i i| ≤
      (j/Fintype.card ι)*(opNorm U*opNorm V*opNorm Q) := by
  rw [matrix_word_contraction]
  have he : (j/Fintype.card ι)*((U*Q) i i*trace V+(U*Vᵀ*Q) i i)-
      j*(trace V/Fintype.card ι)*(U*Q) i i=
      (j/Fintype.card ι)*(U*Vᵀ*Q) i i := by ring
  rw [he,abs_mul,abs_of_nonneg (div_nonneg hj (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (matrix_word_reverse_bound U V Q i) (div_nonneg hj (Nat.cast_nonneg _))
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

structure WordCut (ι : Type*) where
  left : List (WordLetter ι)
  right : List (WordLetter ι)
  inversePartner : Bool

variable {ι : Type*}

def WordCut.prepend (l : WordLetter ι) (c : WordCut ι) : WordCut ι :=
  ⟨l::c.left,c.right,c.inversePartner⟩

def wordPartners (a : ι→ℝ) : List (WordLetter ι)→List (WordCut ι)
  | [] => []
  | l::F => (match l with
      | .diag _ => []
      | .noise => [⟨[],F,false⟩]
      | .inverse => [⟨[.inverse,.diag a],.inverse::F,true⟩]) ++
      (wordPartners a F).map (WordCut.prepend l)

lemma wordPartners_cons (a : ι→ℝ) (l : WordLetter ι) (F : List (WordLetter ι)) :
    wordPartners a (l::F)=(match l with
      | .diag _ => []
      | .noise => [⟨[],F,false⟩]
      | .inverse => [⟨[.inverse,.diag a],.inverse::F,true⟩]) ++
      (wordPartners a F).map (WordCut.prepend l) := rfl

variable [Fintype ι] [DecidableEq ι]

lemma actualWord_nil (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M : Matrix ι ι ℝ) : actualWord f R hR j a z [] M=1 := rfl
lemma actualWord_cons (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M : Matrix ι ι ℝ) (l : WordLetter ι) (F : List (WordLetter ι)) :
    actualWord f R hR j a z (l::F) M=l.eval f R hR j a z M*actualWord f R hR j a z F M := rfl

def WordCut.value (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M E : Matrix ι ι ℝ) (c : WordCut ι) : Matrix ι ι ℝ :=
  (if c.inversePartner then z else 1) •
    (actualWord f R hR j a z c.left M*E*actualWord f R hR j a z c.right M)

lemma WordCut.value_prepend (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M E : Matrix ι ι ℝ) (l : WordLetter ι) (c : WordCut ι) :
    (c.prepend l).value f hR j a z M E=l.eval f R hR j a z M*c.value f hR j a z M E := by
  simp only [WordCut.value,WordCut.prepend,actualWord_cons,Matrix.mul_smul,mul_assoc]
  rfl

theorem actualWordDirection_partners (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (M E : Matrix ι ι ℝ) (F : List (WordLetter ι)) :
    actualWordDirection f R hR j a z M E F=
      ((wordPartners a F).map (WordCut.value f hR j a z M E)).sum := by
  induction F with
  | nil => rfl
  | cons l F ih =>
    rw [actualWordDirection,ih]
    rw [wordPartners_cons a l F,List.map_append,List.sum_append]
    have hm : (((wordPartners a F).map (WordCut.prepend l)).map (WordCut.value f hR j a z M E)).sum=
        l.eval f R hR j a z M*((wordPartners a F).map (WordCut.value f hR j a z M E)).sum := by
      simp only [List.map_map,Function.comp_def,WordCut.value_prepend,List.sum_map_mul_left]
    rw [hm]
    congr 1
    cases l with
    | diag d => simp [WordLetter.direction]
    | noise => simp [WordLetter.direction,WordCut.value,actualWord_nil]
    | inverse =>
      simp only [WordLetter.direction,WordCut.value,ite_true,List.map_cons,
        List.map_nil,List.sum_cons,List.sum_nil,add_zero,actualWord_cons,actualWord_nil,
        WordLetter.eval,mul_one,Matrix.smul_mul,mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
def ordinaryCount (F : List (WordLetter ι)) : ℕ :=
  F.countP (fun l=>match l with | .noise=>true | _=>false)
omit [Fintype ι] [DecidableEq ι] in
def inverseCount (F : List (WordLetter ι)) : ℕ :=
  F.countP (fun l=>match l with | .inverse=>true | _=>false)

omit [Fintype ι] [DecidableEq ι] in
lemma wordPartners_counts (a : ι→ℝ) (F : List (WordLetter ι)) (c : WordCut ι)
    (hc : c∈wordPartners a F) :
    ordinaryCount c.left+ordinaryCount c.right+(if c.inversePartner then 0 else 1)=ordinaryCount F ∧
    inverseCount c.left+inverseCount c.right=inverseCount F+(if c.inversePartner then 1 else 0) := by
  induction F generalizing c with
  | nil => simp [wordPartners] at hc
  | cons l F ih =>
    rw [wordPartners_cons a l F,List.mem_append] at hc
    rcases hc with hc|hc
    · cases l with
      | diag d => simp at hc
      | noise =>
        simp only [List.mem_singleton] at hc
        subst c
        simp [ordinaryCount,inverseCount]
      | inverse =>
        simp only [List.mem_singleton] at hc
        subst c
        simp [ordinaryCount,inverseCount]
        omega
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      obtain ⟨h1,h2⟩ := ih d hd
      cases hf : d.inversePartner <;> cases l <;>
        simp [WordCut.prepend,ordinaryCount,inverseCount,hf] at * <;> omega
end SKGap
end
end

end OAI
