import Mathlib
import OAI.Probability.SKGap.Matrix.PolynomialCoeListSum
import OAI.Probability.SKGap.Localization.PrimaryPrediction

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open WordSeries
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma wordPrediction_lift (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (F : List (Letter (ι→ℝ))) (i : ι) :
    wordPrediction j a z (liftWord F) i=Diagram.prediction j F i := by
  have h := literalSeries_eq_wordPredictionPolynomial j a (liftWord F) (by simp) i
  rw [literalSeries_lift] at h
  have hp : wordPredictionPolynomial j a (liftWord F) i=Polynomial.C (ordinary j F i) := by
    apply Polynomial.ext
    intro k
    have hc := congrArg (PowerSeries.coeff k) h
    simpa only [← Polynomial.coe_C,Polynomial.coeff_coe] using hc.symm
  rw [← (wordPredictionPolynomial_spec j a (liftWord F) i).2 z,hp]
  rw [Polynomial.eval_C]
  have hm (d : Diagram (ι→ℝ)) : d.map id=d := by
    induction d <;> simp [Diagram.map, *]
  simp only [ordinary,Diagram.expect,Diagram.evaluate,Diagram.prediction,hm]

def matrixLetter (J : Matrix ι ι ℝ) : Letter (ι→ℝ) → Matrix ι ι ℝ
  | .diag a => Matrix.diagonal a
  | .noise => J

def matrixWord (J : Matrix ι ι ℝ) (F : List (Letter (ι→ℝ))) : Matrix ι ι ℝ :=
  (F.map (matrixLetter J)).prod

def matrixPolynomial (J : Matrix ι ι ℝ) (P : WordPolynomial (ι:=ι)) : Matrix ι ι ℝ :=
  (P.map (fun p => p.1 • matrixWord J p.2)).sum

lemma exactWord_lift (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (F : List (Letter (ι→ℝ))) :
    exactWord j a (liftWord F) J=matrixWord J F := by
  induction F with
  | nil => rfl
  | cons l F ih =>
    cases l <;> simp [liftWord,Letter.toWord,exactWord,matrixFactorProduct,
      WordLetter.exactEval,matrixWord,matrixLetter] at * <;> exact congrArg _ ih

lemma matrixWord_append (J : Matrix ι ι ℝ) (F G : List (Letter (ι→ℝ))) :
    matrixWord J (F++G)=matrixWord J F*matrixWord J G := by simp [matrixWord]
lemma matrixPolynomial_append (J : Matrix ι ι ℝ) (P Q : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (P++Q)=matrixPolynomial J P+matrixPolynomial J Q := by
  simp [matrixPolynomial]
lemma matrixPolynomial_prefix (J : Matrix ι ι ℝ) (F : List (Letter (ι→ℝ)))
    (P : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (prependWords F P)=matrixWord J F*matrixPolynomial J P := by
  induction P with
  | nil => simp [prependWords,matrixPolynomial]
  | cons p P ih =>
    simp only [prependWords,List.map_cons,matrixPolynomial,List.sum_cons] at *
    rw [matrixWord_append,ih,mul_add,mul_smul_comm]
lemma matrixPolynomial_scale (J : Matrix ι ι ℝ) (c : ℝ) (P : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (scale c P)=c • matrixPolynomial J P := by
  induction P with
  | nil => simp [scale,matrixPolynomial]
  | cons p P ih =>
    simp only [scale,List.map_cons,matrixPolynomial,List.sum_cons] at *
    rw [ih,smul_add,mul_smul]

def primaryMatrix (j : ℝ) (J : Matrix ι ι ℝ) (a : ℕ→ι→ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => 1
  | 1 => J
  | n+2 => J*Matrix.diagonal (a n)*primaryMatrix j J a (n+1) -
      (j*Diagram.mean (a n)) • (Matrix.diagonal (previousDiagonal a n)*primaryMatrix j J a n)

lemma primaryPolynomial_matrix (j : ℝ) (J : Matrix ι ι ℝ) (a : ℕ→ι→ℝ) (n : ℕ) :
    matrixPolynomial J (primaryPolynomial j a n)=primaryMatrix j J a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [primaryPolynomial,matrixPolynomial,primaryMatrix,matrixWord]
  | one => simp [primaryPolynomial,matrixPolynomial,primaryMatrix,matrixWord,matrixLetter]
  | more n hn hn1 =>
    simp only [primaryPolynomial,matrixPolynomial_append,matrixPolynomial_prefix,
      matrixPolynomial_scale,hn,hn1,primaryMatrix,matrixWord,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one,matrixLetter]
    simp [mul_assoc,sub_eq_add_neg,neg_smul]

lemma matrixWordSeminorm_zero (p : Bool) : matrixWordSeminorm (ι:=ι) p 0=0 := by
  let : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
  have hd : diagonalVector (0 : Matrix ι ι ℝ)=0 := by ext i; rfl
  have ho : offDiagonalVector (0 : Matrix ι ι ℝ)=0 := by ext ⟨i,k⟩; simp [offDiagonalVector]
  cases p <;> simp [matrixWordSeminorm,diagonalSeminorm,offDiagonalSeminorm,hd,ho]
lemma matrixWordSeminorm_smul (p : Bool) (c : ℝ) (J : Matrix ι ι ℝ) :
    matrixWordSeminorm p (c • J)=|c| *matrixWordSeminorm p J := by
  let : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
  have hd : diagonalVector (c • J)=c • diagonalVector J := by ext i; rfl
  have ho : offDiagonalVector (c • J)=c • offDiagonalVector J := by
    ext ⟨i,k⟩
    by_cases h : i=k <;> simp [offDiagonalVector,h]
  cases p
  · simp [matrixWordSeminorm,diagonalSeminorm,hd,norm_smul,Real.norm_eq_abs]
  · simp [matrixWordSeminorm,offDiagonalSeminorm,ho,norm_smul,Real.norm_eq_abs]

lemma matrixWordSeminorm_list_sum (p : Bool) (L : List (Matrix ι ι ℝ)) :
    matrixWordSeminorm p L.sum≤(L.map (matrixWordSeminorm p)).sum := by
  induction L with
  | nil => simp [matrixWordSeminorm_zero]
  | cons M L ih =>
    simp only [List.sum_cons,List.map_cons]
    exact (matrixWordSeminorm_add p M L.sum).trans (add_le_add_right ih _)

def coefficientMass (P : WordPolynomial (ι:=ι)) : ℝ := (P.map (fun p=>|p.1|)).sum

lemma polynomial_error (p : Bool) (j : ℝ) (J : Matrix ι ι ℝ)
    (P : WordPolynomial (ι:=ι)) {C : ℝ}
    (h : ∀ t∈P, matrixWordSeminorm p
      (matrixWord J t.2-Matrix.diagonal (Diagram.prediction j t.2))≤C) :
    matrixWordSeminorm p (matrixPolynomial J P-Matrix.diagonal (polynomialPrediction j P))≤
      coefficientMass P*C := by
  induction P with
  | nil => simp [matrixPolynomial,polynomialPrediction,coefficientMass,matrixWordSeminorm_zero]
  | cons t P ih =>
    have he : matrixPolynomial J (t::P)-Matrix.diagonal (polynomialPrediction j (t::P))=
        t.1 • (matrixWord J t.2-Matrix.diagonal (Diagram.prediction j t.2))+
        (matrixPolynomial J P-Matrix.diagonal (polynomialPrediction j P)) := by
      have hp : polynomialPrediction j (t::P)=
          t.1 • Diagram.prediction j t.2+polynomialPrediction j P := by
        ext i; simp [polynomialPrediction]
      have hd (u v : ι→ℝ) : Matrix.diagonal (u+v)=Matrix.diagonal u+Matrix.diagonal v :=
        (Matrix.diagonal_add u v).symm
      simp only [matrixPolynomial,List.map_cons,List.sum_cons,hp,hd,Matrix.diagonal_smul]
      rw [smul_sub]
      abel
    rw [he]
    calc
      _ ≤ matrixWordSeminorm p (t.1 • (matrixWord J t.2-Matrix.diagonal (Diagram.prediction j t.2)))+
          matrixWordSeminorm p (matrixPolynomial J P-Matrix.diagonal (polynomialPrediction j P)) :=
        matrixWordSeminorm_add _ _ _
      _ ≤ |t.1| *C+coefficientMass P*C := by
        rw [matrixWordSeminorm_smul]
        exact add_le_add (mul_le_mul_of_nonneg_left (h t (by simp)) (abs_nonneg _))
          (ih (fun q hq=>h q (List.mem_cons_of_mem _ hq)))
      _ = coefficientMass (t::P)*C := by simp [coefficientMass,add_mul]

theorem primaryMatrix_seminorm (p : Bool) (j : ℝ) (J : Matrix ι ι ℝ)
    (a : ℕ→ι→ℝ) (n : ℕ) (hn : 0<n) {C : ℝ}
    (h : ∀ t∈primaryPolynomial j a n, matrixWordSeminorm p
      (matrixWord J t.2-Matrix.diagonal (Diagram.prediction j t.2))≤C) :
    matrixWordSeminorm p (primaryMatrix j J a n)≤coefficientMass (primaryPolynomial j a n)*C := by
  have hz : polynomialPrediction j (primaryPolynomial j a n)=0 :=
    funext (primaryPolynomial_prediction_zero j a n hn)
  simpa only [primaryPolynomial_matrix,hz,Matrix.diagonal_zero',sub_zero] using
    polynomial_error p j J (primaryPolynomial j a n) h

omit [DecidableEq ι]

omit [Fintype ι] in
lemma coefficientMass_nonneg (P : WordPolynomial (ι:=ι)) : 0≤coefficientMass P :=
  List.sum_nonneg (by intro x hx; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
omit [Fintype ι] in
lemma coefficientMass_append (P Q : WordPolynomial (ι:=ι)) :
    coefficientMass (P++Q)=coefficientMass P+coefficientMass Q := by simp [coefficientMass]
omit [Fintype ι] in
lemma coefficientMass_prefix (F : List (Letter (ι→ℝ))) (P : WordPolynomial (ι:=ι)) :
    coefficientMass (prependWords F P)=coefficientMass P := by
  simp [coefficientMass,prependWords,Function.comp_def]
omit [Fintype ι] in
lemma coefficientMass_scale (c : ℝ) (P : WordPolynomial (ι:=ι)) :
    coefficientMass (scale c P)=|c| *coefficientMass P := by
  simp [coefficientMass,scale,Function.comp_def,abs_mul,List.sum_map_mul_left]

lemma mean_abs_le_one [Nonempty ι] {a : ι→ℝ} (ha : ∀ i,|a i|≤1) :
    |Diagram.mean a|≤1 := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    |Diagram.mean a| = |∑ i,a i|/(Fintype.card ι:ℝ) := by
      rw [Diagram.mean,abs_div,abs_of_pos hn]
    _ ≤ (∑ i,|a i|)/(Fintype.card ι:ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn.le
    _ ≤ 1 := by
      rw [div_le_one hn]
      simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => ha i)

def massBound (j : ℝ) : ℕ→ℝ
  | 0 => 1
  | 1 => 1
  | n+2 => massBound j (n+1)+|j| *massBound j n
lemma massBound_pos (j : ℝ) (n : ℕ) : 0< massBound j n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [massBound]
  | one => norm_num [massBound]
  | more n hn hn1 => exact add_pos_of_pos_of_nonneg hn1 (mul_nonneg (abs_nonneg _) hn.le)
lemma primaryMass_bound [Nonempty ι] (j : ℝ) (a : ℕ→ι→ℝ)
    (ha : ∀ n i,|a n i|≤1) (n : ℕ) :
    coefficientMass (primaryPolynomial j a n)≤ massBound j n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [primaryPolynomial,coefficientMass,massBound]
  | one => simp [primaryPolynomial,coefficientMass,massBound]
  | more n hn hn1 =>
    simp only [primaryPolynomial,coefficientMass_append,coefficientMass_prefix,
      coefficientMass_scale,abs_neg,abs_mul,massBound]
    apply add_le_add hn1
    calc
      |j| * |Diagram.mean (a n)| * coefficientMass (primaryPolynomial j a n) ≤
          |j| * 1 * coefficientMass (primaryPolynomial j a n) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mean_abs_le_one (ha n)) (abs_nonneg _))
          (coefficientMass_nonneg _)
      _ ≤ |j| * massBound j n := by simpa using mul_le_mul_of_nonneg_left hn (abs_nonneg j)

lemma primaryPolynomial_admissible (j : ℝ) (a : ℕ→ι→ℝ)
    (ha : ∀ n i,|a n i|≤1) (n : ℕ) :
    ∀ t∈primaryPolynomial j a n, t.2.length≤2*n ∧
      ∀ l∈liftWord t.2,l.bounded 1 := by
  have hp (n : ℕ) : ∀ i,|previousDiagonal a n i|≤1 := by
    cases n <;> simp [previousDiagonal,ha]
  induction n using Nat.twoStepInduction with
  | zero => simp [primaryPolynomial,liftWord]
  | one =>
    intro t ht
    simp only [primaryPolynomial,List.mem_singleton] at ht
    subst t
    simp [liftWord,Letter.toWord,WordLetter.bounded]
  | more n hn hn1 =>
    intro t ht
    simp only [primaryPolynomial,List.mem_append,prependWords,scale,List.mem_map] at ht
    rcases ht with ⟨q,hq,rfl⟩ | ⟨u,⟨q,hq,rfl⟩,rfl⟩
    · obtain ⟨hql,hqb⟩ := hn1 q hq
      constructor
      · simp only [List.length_append,List.length_cons,List.length_nil]; omega
      · intro l hl
        simp only [liftWord_append,liftWord_cons,liftWord_nil,Letter.toWord,
          List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with (rfl|rfl)|hl
        · trivial
        · exact ha n
        · exact hqb l hl
    · obtain ⟨hql,hqb⟩ := hn q hq
      constructor
      · simp only [List.length_append,List.length_cons,List.length_nil]; omega
      · intro l hl
        simp only [liftWord_append,liftWord_cons,liftWord_nil,Letter.toWord,
          List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl|hl
        · exact hp n
        · exact hqb l hl

end SKGap.Noncrossing.Primary
end
end

end OAI
