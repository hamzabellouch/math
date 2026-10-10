import Mathlib
import OAI.Probability.SKGap.Localization.FiniteRecipeControl

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix MeasureTheory ProbabilityTheory Real Set
open SKGap.Noncrossing.Primary

variable {n : ℕ}
def formalOpBound (j R : ℝ) : ℕ→ℝ
  | 0 => 1
  | 1 => R
  | k+2 => R*formalOpBound j R (k+1)+|j| *formalOpBound j R k

lemma formalOpBound_nonneg (j : ℝ) {R : ℝ} (hR : 0≤R) (k : ℕ) :
    0≤formalOpBound j R k := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [formalOpBound]
  | one => exact hR
  | more k hk hk1 => dsimp only [formalOpBound]; positivity

lemma primaryMatrix_opNorm {j R : ℝ} (J : Interaction n) (a : ℕ→Fin n→ℝ)
    (hn : 0<n) (hR : 0≤R) (hJ : SKGap.opNorm J≤R) (ha : ∀ l i,|a l i|≤1) (k : ℕ) :
    SKGap.opNorm (primaryMatrix j J a k)≤formalOpBound j R k := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hd (l : ℕ) : SKGap.opNorm (Matrix.diagonal (a l))≤1 :=
    SKGap.opNorm_diagonal_le zero_le_one (ha l)
  have hp (l : ℕ) : SKGap.opNorm (Matrix.diagonal (previousDiagonal a l))≤1 := by
    apply SKGap.opNorm_diagonal_le zero_le_one
    cases l with
    | zero => simp [previousDiagonal]
    | succ l => exact ha l
  induction k using Nat.twoStepInduction with
  | zero => exact SKGap.opNorm_one_le
  | one => exact hJ
  | more k hk hk1 =>
    dsimp only [primaryMatrix,formalOpBound]
    apply (SKGap.opNorm_sub _ _).trans
    apply add_le_add
    · apply (SKGap.opNorm_mul _ _).trans
      have hJD : SKGap.opNorm (J*Matrix.diagonal (a k))≤R :=
        (SKGap.opNorm_mul _ _).trans ((mul_le_mul hJ (hd k) (norm_nonneg _) hR).trans_eq (mul_one _))
      exact mul_le_mul hJD hk1 (norm_nonneg _) hR
    · rw [opNorm_smul,abs_mul]
      have hm : SKGap.opNorm (Matrix.diagonal (previousDiagonal a k)*primaryMatrix j J a k)≤
          formalOpBound j R k :=
        (SKGap.opNorm_mul _ _).trans ((mul_le_mul (hp k) hk (norm_nonneg _)
          zero_le_one).trans_eq (one_mul _))
      calc
        _ ≤ (|j| *1)*formalOpBound j R k := mul_le_mul
          (mul_le_mul_of_nonneg_left (mean_abs_le_one (ha k)) (abs_nonneg _)) hm
          (norm_nonneg _) (by positivity)
        _ = _ := by ring

def primaryWordTail (j : ℝ) (k n : ℕ) : ENNReal :=
  2*((wordPatternSet (2*k) (2*k)).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
    ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2)))+
    (ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))+
      ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n))))))
def primaryNormTail (j : ℝ) (n : ℕ) : ENNReal :=
  ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))+
    ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n))))

theorem primary_uniform_actual_derivatives {j : ℝ} (hj : 0<j) (hj1 : j<1) (k : ℕ) :
    ∃ B : ℝ,∃ N : ℕ,0<B ∧ 0<N ∧ ∀ n,N≤n →
      let R := 2*sqrt j+1+1
      let C := differentiationBound j R B k
      let T := C+8*C^2
      (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ∃ (h : Fin n→ℝ) (x : Spin n),
          let J := removeDiagonal (goeMatrix (j/n) g)
          ¬ (‖derivativeMatrix (primaryState j J h k).2 x-formalField j J h x k‖≤C ∧
            ‖derivativeMatrix (primaryState j J h k).1 x-formalMag j J h x k‖≤C ∧
            SKGap.opNorm (derivativeMatrix (primaryState j J h k).1 x)≤C ∧
            ShapeBound (derivativeMatrix (primaryState j J h k).2 x) C ∧
            (n:ℝ)*‖derivativeVector (siteMean (fun y i =>
              scalarVariance ((primaryState j J h k).2 y i))) x‖^2≤(2*T+4*T^2)^2)} ≤
        primaryNormTail j n+∑ l : Fin (k+1),primaryWordTail j (l.val+1) n := by
  classical
  have hchoice (l : Fin (k+1)) := primary_uniform_two_seminorms hj hj1 (l.val+1) (by omega)
  choose c N hc hN hbound using hchoice
  let R := 2*sqrt j+1+1
  have hR : 0≤R := by dsimp [R]; positivity
  let B := 1+∑ l : Fin (k+1), (c l+formalOpBound j R (l.val+1))
  have hB : 0<B := by
    dsimp [B]
    have hs : 0≤∑ l : Fin (k+1), (c l+formalOpBound j R (l.val+1)) :=
      Finset.sum_nonneg (fun l _ => add_nonneg (hc l).le (formalOpBound_nonneg j hR _))
    linarith
  have hcB (l : Fin (k+1)) : c l≤B := by
    have hs := Finset.single_le_sum (s:=Finset.univ)
      (fun q (_ : q∈Finset.univ) => add_nonneg (hc q).le (formalOpBound_nonneg j hR (q.val+1)))
      (Finset.mem_univ l)
    have hp := formalOpBound_nonneg j hR (l.val+1)
    dsimp [B]; linarith
  have hoB (l : Fin (k+1)) : formalOpBound j R (l.val+1)≤B := by
    have hs := Finset.single_le_sum (s:=Finset.univ)
      (fun q (_ : q∈Finset.univ) => add_nonneg (hc q).le (formalOpBound_nonneg j hR (q.val+1)))
      (Finset.mem_univ l)
    have hp := hc l
    dsimp [B]; linarith
  let N₀ := 1+∑ l : Fin (k+1),N l
  refine ⟨B,N₀,hB,by dsimp [N₀]; omega,?_⟩
  intro n hn
  have hn0 : 0<n := by
    have : 0<N₀ := by dsimp [N₀]; omega
    omega
  have hNl (l : Fin (k+1)) : N l≤n := by
    have hs := Finset.single_le_sum (f:=N) (s:=Finset.univ) (by intros; omega) (Finset.mem_univ l)
    dsimp [N₀] at hn; omega
  let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)
  let A : Fin (k+1) → Set (MatrixCoordinates (Fin n)→ℝ) := fun l =>
    {g | ∃ (p : Bool) (a : ℕ→Fin n→ℝ), (∀ d i,|a d i|≤1) ∧
      c l < matrixWordSeminorm p (primaryMatrix j (removeDiagonal (goeMatrix (j/n) g)) a (l.val+1))}
  let E : Set (MatrixCoordinates (Fin n)→ℝ) :=
    {g | R<SKGap.opNorm (removeDiagonal (goeMatrix (j/n) g))}
  have hA (l : Fin (k+1)) : μ (A l)≤primaryWordTail j (l.val+1) n := hbound l n (hNl l)
  have hE : μ E≤primaryNormTail j n := zeroDiagGOE_norm_tail hj hn0
  apply (measure_mono (t:=E∪⋃ l,A l) ?_).trans
    ((measure_union_le _ _).trans ((add_le_add hE
      ((measure_iUnion_fintype_le μ A).trans (Finset.sum_le_sum (fun l _ => hA l))))))
  intro g hg
  by_contra hbad
  have hJ : SKGap.opNorm (removeDiagonal (goeMatrix (j/n) g))≤R := by
    apply le_of_not_gt; intro hh; exact hbad (.inl hh)
  obtain ⟨h,x,hfail⟩ := hg
  have hf : ∀ l≤k,ShapeBound (formalField j (removeDiagonal (goeMatrix (j/n) g)) h x l) B := by
    intro l hl
    let q : Fin (k+1) := ⟨l,by omega⟩
    have ha := primaryDiagonal_bounded j (removeDiagonal (goeMatrix (j/n) g)) h x
    refine ⟨(primaryMatrix_opNorm _ _ hn0 hR hJ ha (l+1)).trans (hoB q),?_,?_⟩
    · apply (le_of_not_gt ?_).trans (hcB q)
      intro hh
      apply hbad
      exact .inr (Set.mem_iUnion.mpr ⟨q,false,_,ha,hh⟩)
    · apply (le_of_not_gt ?_).trans (hcB q)
      intro hh
      apply hbad
      exact .inr (Set.mem_iUnion.mpr ⟨q,true,_,ha,hh⟩)
  obtain ⟨h1,h2,h3,h4⟩ := primary_differentiation _ h x hn0 hR hB.le hJ k hf
  exact hfail ⟨h1,h2,h3,h4,primary_average_differentiation _ h x hn0 hR hB.le hJ k hf⟩

end SKGapCutoff.Primary

end
end

end OAI
