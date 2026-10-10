import Mathlib
import OAI.Probability.SKGap.Localization.GramColumnBounds

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma matrixBilinear_eq_pair (M : Matrix ι ι ℝ) (x y : EuclideanSpace ℝ ι) :
    matrixBilinear M x y=matrixPair M x.ofLp y.ofLp := by
  simp only [matrixBilinear,matrixPair,dotProduct,Matrix.mulVec,Finset.mul_sum]
  congr 1; ext i; congr 1; ext k; ring

lemma exactG_transpose (j : ℝ) (a : ι → ℝ) {W : Matrix ι ι ℝ} (hW : Wᵀ=W) :
    (exactG j a W)ᵀ=exactG j a W := by
  simp only [exactG,Matrix.transpose_mul,Matrix.transpose_nonsing_inv,
    Matrix.transpose_sub,Matrix.transpose_one,Matrix.transpose_smul,hW,
    pathDiagonal,Matrix.diagonal_transpose,Matrix.mul_assoc]

def augmentedGramTolerance (B ε : ℝ) : ℝ :=
  4*(ε+(sqrt B)⁻¹*(1+B)*ε+B⁻¹*(1+2*B+B^2)*ε)

def actualAugmentedGram {n : ℕ} (j : ℝ) (a : Fin n → ℝ)
    (p : Fin 3 → EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n))
    (g : MatrixCoordinates (Fin n) → ℝ) : Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ :=
  let B := j/(n:ℝ)*∑ i,a i
  let W := goeMatrix (j/(n:ℝ)) g
  let V := extendColumns (fun r => (p r).ofLp) (residualGramVector B W u.ofLp)
  Vᵀ*exactG j a W*V

def diagonalAugmentedGram {n : ℕ} (a : Fin n → ℝ)
    (p : Fin 3 → EuclideanSpace ℝ (Fin n)) :
    Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ :=
  fromBlocks (fun r s => matrixPair (diagonal a) (p r).ofLp (p s).ofLp) 0 0 1

theorem conditional_augmented_gram_tail {j A U ε : ℝ}
    (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1) (hU : 0 ≤ U) (hε : 0 < ε) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 0 < N ∧
      ∀ n, N ≤ n → ∀ a : Fin n → ℝ, (∀ i,0 ≤ a i) → (∀ i,a i ≤ A) →
      0 < j/(n:ℝ)*∑ i,a i →
      ∀ (p : Fin 3 → EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n)),
      (∀ r,‖p r‖ ≤ U) → ‖u‖ ≤ U → u.ofLp⬝ᵥu.ofLp=1 →
      (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
        {g | ¬bilinearPathGood j A a g ∨
          augmentedGramTolerance (j/(n:ℝ)*∑ i,a i) ε <
            ‖actualAugmentedGram j a p u g-diagonalAugmentedGram a p‖} ≤
        99*Real.exp (-c*(n:ℝ)) := by
  obtain ⟨c,N,hc,hN,ht⟩ := bilinear_deterministic_equivalents hj hA hs hU hε 4
  refine ⟨c,N,hc,hN,?_⟩
  intro n hn a ha haA hB p u hp hu hunit
  let v : Fin 4 → EuclideanSpace ℝ (Fin n) := Fin.cons u p
  have hv : ∀ r,‖v r‖ ≤ U := by
    intro r
    refine Fin.cases hu (fun r => hp r) r
  have hh := ht n hn a ha haA v hv
  apply (measureReal_mono (s₂ := {g | ¬bilinearPathGood j A a g ∨ ∃ r s k,
      ε < |matrixBilinear (bilinearError k j a (goeMatrix (j/(n:ℝ)) g)) (v r) (v s)|})
    ?_ (measure_ne_top _ _)).trans (by norm_num only [Nat.cast_ofNat,show (3:ℝ)+6*4^2=99 by norm_num] at hh; exact hh)
  intro g hg
  by_contra hbad
  change ¬(¬bilinearPathGood j A a g ∨ ∃ r s k,
    ε < |matrixBilinear (bilinearError k j a (goeMatrix (j/(n:ℝ)) g)) (v r) (v s)|) at hbad
  push Not at hbad
  rcases hbad with ⟨hpath,hpair⟩
  have he (r s : Fin 4) (k : Fin 3) :
      |matrixPair (bilinearError k j a (goeMatrix (j/(n:ℝ)) g)) (v r).ofLp (v s).ofLp| ≤ ε := by
    rw [← matrixBilinear_eq_pair]
    exact hpair r s k
  have h00 (r s : Fin 3) := he r.succ s.succ 0
  have h0u (r : Fin 3) := he r.succ 0 0
  have h1u (r : Fin 3) := he r.succ 0 1
  have h0 := he 0 0 0
  have h1 := he 0 0 1
  have h2 := he 0 0 2
  simp only [v,Fin.cons_succ,Fin.cons_zero,bilinearError,ite_true,ite_false,
    Fin.reduceEq,Fintype.card_fin] at h00 h0u h1u h0 h1 h2
  have hb := augmented_gram_error (exactG_transpose j a (goeMatrix_transpose _ g))
    (goeMatrix_transpose _ g) (diagonal a) hB hε.le (fun r => (p r).ofLp) u.ofLp hunit
    h00 h0u h1u h0 h1 h2
  have hb' : ‖actualAugmentedGram j a p u g-diagonalAugmentedGram a p‖ ≤
      augmentedGramTolerance (j/(n:ℝ)*∑ i,a i) ε := by
    simpa only [actualAugmentedGram,diagonalAugmentedGram,augmentedGramTolerance,
      Fintype.card_fin,Nat.cast_ofNat,show (3:ℝ)+1=4 by norm_num] using hb
  exact hg.elim (fun hn => hn hpath) (fun he => not_lt_of_ge hb' he)
end SKGap
end
end

end OAI
