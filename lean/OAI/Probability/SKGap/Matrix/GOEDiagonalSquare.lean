import Mathlib
import OAI.Probability.SKGap.Gaussian.GOEGaussian
import OAI.Probability.SKGap.Matrix.WordBiasCutoff

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

lemma gaussian_goe_centered {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ)
    (x : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    matrixCentered (fun y : EuclideanSpace ℝ (MatrixCoordinates ι)=>goeMatrix r y) x=goeMatrix r x := by
  have hm : matrixEntryMean (fun y : EuclideanSpace ℝ (MatrixCoordinates ι)=>goeMatrix r y)=0 := by
    ext i k
    exact goe_mean_zero r i k
  simp only [matrixCentered,hm,sub_zero]

theorem goe_diagonal_frobenius_tail {j : ℝ} (hj : 0<j) {n : ℕ} (hn : 1≤n) :
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | matrixNormConstant*sqrt (2*j)+1<
        ‖Matrix.diagonal (fun i=>goeMatrix (j/n) g i i)‖}≤
      ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2))) := by
  have hs : 0<sqrt (2*j) := sqrt_pos.mpr (by positivity)
  have hL : LipschitzWith (Real.toNNReal (sqrt (2*j)*1/sqrt n))
      (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>goeMatrix (j/n) x) := by
    apply (goeMatrix_L2_lipschitz (j/n)).weaken
    change sqrt (2*(j/n))≤(Real.toNNReal (sqrt (2*j)*1/sqrt n):ℝ)
    rw [Real.coe_toNNReal _ (by positivity),mul_one,show 2*(j/n)=(2*j)/n by ring,Real.sqrt_div (by positivity)]
  have ht := gaussianMatrix_scaled_semnorm_tail hn hs (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1) hL false
  simpa only [one_pow,mul_one,gaussian_goe_centered,matrixWordSeminorm,Bool.false_eq_true,ite_false,
    Matrix.frobenius_norm_diagonal,diagonalSeminorm,diagonalVector] using ht
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def removeDiagonal (M : Matrix ι ι ℝ) : Matrix ι ι ℝ := M-Matrix.diagonal (fun i=>M i i)
lemma matrixWordSeminorm_le (p : Bool) (M : Matrix ι ι ℝ) : matrixWordSeminorm p M≤‖M‖ := by
  cases p
  · exact diagonalSeminorm_le M
  · exact offDiagonalSeminorm_le M

lemma actualWord_removeDiagonal [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (L : ℕ) (F : List (WordLetter ι))
    (hFL : F.length≤L) (hF : ∀ l∈F,l.bounded D) (M : Matrix ι ι ℝ) :
    ‖actualWord f R hR j a 1 F (removeDiagonal M)-actualWord f R hR j a 1 F M‖≤
      (L:ℝ)*(actualWordBound f R j A D)^L*‖Matrix.diagonal (fun i=>M i i)‖ := by
  have hB : 1≤actualWordBound f R j A D := by
    have hh := path_constants_nonneg f hR hj hA
    unfold actualWordBound
    linarith
  have ht := ((actualWord_bounds f hR hj hA hD ha haA
    (show (1:ℝ)∈Icc 0 1 from ⟨zero_le_one,le_rfl⟩) F hF).2).dist_le_mul (removeDiagonal M) M
  have hd : ‖removeDiagonal M-M‖=‖Matrix.diagonal (fun i=>M i i)‖ := by
    rw [show removeDiagonal M-M= -Matrix.diagonal (fun i=>M i i) by unfold removeDiagonal;abel,norm_neg]
  simp only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_natCast,hd] at ht
  apply ht.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul (by exact_mod_cast hFL) (pow_le_pow_right₀ hB hFL)
    (pow_nonneg (zero_le_one.trans hB) _) (Nat.cast_nonneg _)

theorem actual_word_simultaneous_zerodiag_of_cutoff {j A D : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (L : ℕ) (f : 𝓢(ℝ,ℂ))
    (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
    (hR : 0≤2*sqrt j+1+1) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧
      ∀ n,N≤n → ∀ p : Bool,
        (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
          (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
          C< matrixWordSeminorm p
            (actualWord f (2*sqrt j+1+1) hR j a 1 F (removeDiagonal (goeMatrix (j/n) g))-
              Matrix.diagonal (wordPrediction j a 1 F))} ≤
          (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
            ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2))) := by
  obtain ⟨C,N,hC,hN,hw⟩ := actual_word_simultaneous_prediction_of_cutoff hj hA hs hD hAD L f hf hR
  let R := 2*sqrt j+1+1
  let B := actualWordBound f R j A D
  let T := matrixNormConstant*sqrt (2*j)+1
  have hD0 := zero_le_one.trans hD
  have hB : 0≤B := (actualWordBound_pos f hR hj.le hA.le hD0).le
  have hT : 0≤T := by
    have hc := matrixNormConstant_bounds.1
    dsimp [T]
    positivity
  let K := (L:ℝ)*B^L*T
  have hK : 0≤K := by dsimp [K];positivity
  refine ⟨C+K,N,by linarith,hN,?_⟩
  intro n hn p
  have hn0 : 0<n := hN.trans_le hn
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  let E := {g : MatrixCoordinates (Fin n)→ℝ | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
    (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
      C < matrixWordSeminorm p (actualWord f R hR j a 1 F (goeMatrix (j/n) g)-Matrix.diagonal (wordPrediction j a 1 F))}
  let V := {g : MatrixCoordinates (Fin n)→ℝ | T<‖Matrix.diagonal (fun i=>goeMatrix (j/n) g i i)‖}
  have hsub : {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
      (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
      C+K < matrixWordSeminorm p (actualWord f R hR j a 1 F (removeDiagonal (goeMatrix (j/n) g))-
        Matrix.diagonal (wordPrediction j a 1 F))}⊆E∪V := by
    intro g hg
    by_contra hh
    obtain ⟨a,F,ha,hFL,hF,hI,hbad⟩ := hg
    have hd : ‖Matrix.diagonal (fun i=>goeMatrix (j/n) g i i)‖≤T := by
      by_contra hd
      exact hh (Or.inr (lt_of_not_ge hd))
    have he : matrixWordSeminorm p (actualWord f R hR j a 1 F (goeMatrix (j/n) g)-Matrix.diagonal (wordPrediction j a 1 F))≤C := by
      by_contra he
      exact hh (Or.inl ⟨a,F,ha,hFL,hF,hI,lt_of_not_ge he⟩)
    have hp := (matrixWordSeminorm_le p _).trans (actualWord_removeDiagonal f hR hj.le hA.le hD0
      (fun i=>(ha i).1) (fun i=>(ha i).2) L F hFL hF (goeMatrix (j/n) g))
    have hp' : matrixWordSeminorm p
        (actualWord f R hR j a 1 F (removeDiagonal (goeMatrix (j/n) g))-actualWord f R hR j a 1 F (goeMatrix (j/n) g))≤K :=
      hp.trans (mul_le_mul_of_nonneg_left hd (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB _)))
    have hac := matrixWordSeminorm_add p
      (actualWord f R hR j a 1 F (removeDiagonal (goeMatrix (j/n) g))-actualWord f R hR j a 1 F (goeMatrix (j/n) g))
      (actualWord f R hR j a 1 F (goeMatrix (j/n) g)-Matrix.diagonal (wordPrediction j a 1 F))
    rw [sub_add_sub_cancel] at hac
    linarith
  exact (measure_mono hsub).trans ((measure_union_le E V).trans
    (add_le_add (hw n hn p) (goe_diagonal_frobenius_tail hj (Nat.succ_le_iff.mpr hn0))))
end SKGap
end
end

end OAI
