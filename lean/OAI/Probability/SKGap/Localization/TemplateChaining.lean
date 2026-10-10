import Mathlib
import OAI.Probability.SKGap.Brownian.MatrixMeanContinuous
import OAI.Probability.SKGap.Gaussian.GaussianMatrixChaining

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

lemma sqrt_mesh_increment {δ : ℝ} (hδ : 0 ≤ δ) (k : ℕ) (h : δ ≤ 2*(1/4:ℝ)^k) :
    sqrt δ ≤ 2*(1/2:ℝ)^k := by
  have he : (1/4:ℝ)^k=(1/2:ℝ)^k*(1/2:ℝ)^k := by rw [←mul_pow]; norm_num
  rw [he] at h
  have hs := sq_sqrt hδ
  have hp : 0 ≤ (1/2:ℝ)^k := by positivity
  nlinarith [sqrt_nonneg δ]

theorem templateWord_gaussian_chaining {m : ℕ} (f : 𝓢(ℝ,ℂ)) {R j D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,1 ≤ n→∀ p : Bool,
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | ∃ θ : WordParameter m (Fin n),C< matrixWordSeminorm p
        (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
          templateMatrix f R hR j D F θ (goeMatrix (j/n) x)) (WithLp.toLp 2 g))} ≤
      ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  let B : NNReal := ⟨actualWordBound f R j 1 D,(actualWordBound_pos f hR hj zero_le_one hD).le⟩
  let L : NNReal := (F.length:NNReal)*B^F.length
  let V : NNReal := wordMixedCoeff B F.length*⟨templateHolder f R j D,templateHolder_nonneg f hj hD⟩
  let H : ℝ := 1+((L:ℝ)+2*V)*sqrt (2*j)
  let E : ℝ := log 16*((m:ℝ)+1)
  have hH : 0<H := by dsimp [H];positivity
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hHL : (L:ℝ)*sqrt (2*j) ≤ H := by
    dsimp [H]
    nlinarith [NNReal.coe_nonneg V,sqrt_nonneg (2*j)]
  have hHV : 2*(V:ℝ)*sqrt (2*j) ≤ H := by
    dsimp [H]
    nlinarith [NNReal.coe_nonneg L,sqrt_nonneg (2*j)]
  refine ⟨gaussianMatrixChainConstant H E,?_,?_⟩
  · have hc := matrixNormConstant_bounds.1
    dsimp [gaussianMatrixChainConstant]
    have hh : 0 < matrixNormConstant*H := mul_pos (by linarith) hH
    positivity
  · intro n hn p
    let : NeZero n := ⟨by omega⟩
    have hdim : log 16*(Fintype.card (Option (Fin m)×Fin n):ℝ) ≤ E*(n:ℝ) := by
      simp only [Fintype.card_prod,Fintype.card_option,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      dsimp [E]
      ring_nf
      exact le_rfl
    let T : WordParameter m (Fin n)→EuclideanSpace ℝ (MatrixCoordinates (Fin n))→Matrix (Fin n) (Fin n) ℝ :=
      fun θ x=>templateMatrix f R hR j D F θ (goeMatrix (j/n) x)
    have hsqrt : sqrt (2*(j/n))=sqrt (2*j)/sqrt n := by
      rw [show 2*(j/n)=(2*j)/n by ring,Real.sqrt_div (by positivity)]
    have hT (θ : WordParameter m (Fin n)) : LipschitzWith (Real.toNNReal (H/sqrt n)) (T θ) := by
      have hh := (templateMatrix_bounds f hR hj hD F θ).2.comp (goeMatrix_L2_lipschitz (j/n))
      apply hh.weaken
      change (L:ℝ)*sqrt (2*(j/n)) ≤ (Real.toNNReal (H/sqrt n):ℝ)
      rw [Real.coe_toNNReal _ (by positivity),hsqrt]
      calc
        _ = ((L:ℝ)*sqrt (2*j))/sqrt n := by ring
        _ ≤ H/sqrt n := div_le_div_of_nonneg_right hHL (sqrt_nonneg _)
    have hi (k : ℕ) (θ η : WordParameter m (Fin n)) (hθη : dist θ η ≤ 2*(1/4:ℝ)^k) :
        LipschitzWith (Real.toNNReal (H*(1/2:ℝ)^k/sqrt n)) (fun x=>T θ x-T η x) := by
      have hh := (templateMatrix_increments f hR hj hD F θ η).2.comp (goeMatrix_L2_lipschitz (j/n))
      apply hh.weaken
      change (((wordMixedCoeff B F.length:ℝ)*(templateHolder f R j D*sqrt (dist θ η)))*sqrt (2*(j/n))) ≤
        (Real.toNNReal (H*(1/2:ℝ)^k/sqrt n):ℝ)
      rw [Real.coe_toNNReal _ (by positivity),hsqrt]
      have he : (wordMixedCoeff B F.length:ℝ)*(templateHolder f R j D*sqrt (dist θ η))=
          (V:ℝ)*sqrt (dist θ η) := by
        change (wordMixedCoeff B F.length:ℝ)*(templateHolder f R j D*sqrt (dist θ η)) =
          ((wordMixedCoeff B F.length:ℝ)*templateHolder f R j D)*sqrt (dist θ η)
        ring
      rw [he]
      calc
        _ ≤ (V:ℝ)*(2*(1/2:ℝ)^k)*(sqrt (2*j)/sqrt n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sqrt_mesh_increment dist_nonneg k hθη) V.coe_nonneg) (by positivity)
        _ = (2*(V:ℝ)*sqrt (2*j))*(1/2:ℝ)^k/sqrt n := by ring
        _ ≤ H*(1/2:ℝ)^k/sqrt n := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hHV (by positivity)) (sqrt_nonneg _)
    exact gaussianMatrix_box_chaining hn hH hE hdim T hT hi
      (fun g=>templateGaussian_centered_continuous f hR hj hD F (j/n) (WithLp.toLp 2 g)) p
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem generalTemplateWord_gaussian_chaining {m : ℕ} (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,1 ≤ n→∀ p : Bool,
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | ∃ θ : WordParameter m (Fin n),C< matrixWordSeminorm p
        (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
          generalTemplateMatrix f R hR j A D F θ (goeMatrix (j/n) x)) (WithLp.toLp 2 g))} ≤
      ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
  let L : NNReal := (F.length:NNReal)*B^F.length
  let V : NNReal := wordMixedCoeff B F.length*⟨generalTemplateHolder f R j A D,generalTemplateHolder_nonneg f hR hj hA hD⟩
  let H : ℝ := 1+((L:ℝ)+2*V)*sqrt (2*j)
  let E : ℝ := log 16*((m:ℝ)+1)
  have hH : 0<H := by dsimp [H];positivity
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hHL : (L:ℝ)*sqrt (2*j) ≤ H := by
    dsimp [H]
    nlinarith [NNReal.coe_nonneg V,sqrt_nonneg (2*j)]
  have hHV : 2*(V:ℝ)*sqrt (2*j) ≤ H := by
    dsimp [H]
    nlinarith [NNReal.coe_nonneg L,sqrt_nonneg (2*j)]
  refine ⟨gaussianMatrixChainConstant H E,?_,?_⟩
  · have hc := matrixNormConstant_bounds.1
    dsimp [gaussianMatrixChainConstant]
    have hh : 0 < matrixNormConstant*H := mul_pos (by linarith) hH
    positivity
  · intro n hn p
    let : NeZero n := ⟨by omega⟩
    have hdim : log 16*(Fintype.card (Option (Fin m)×Fin n):ℝ) ≤ E*(n:ℝ) := by
      simp only [Fintype.card_prod,Fintype.card_option,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      dsimp [E]
      ring_nf
      exact le_rfl
    let T : WordParameter m (Fin n)→EuclideanSpace ℝ (MatrixCoordinates (Fin n))→Matrix (Fin n) (Fin n) ℝ :=
      fun θ x=>generalTemplateMatrix f R hR j A D F θ (goeMatrix (j/n) x)
    have hsqrt : sqrt (2*(j/n))=sqrt (2*j)/sqrt n := by
      rw [show 2*(j/n)=(2*j)/n by ring,Real.sqrt_div (by positivity)]
    have hT (θ : WordParameter m (Fin n)) : LipschitzWith (Real.toNNReal (H/sqrt n)) (T θ) := by
      have hh := (generalTemplateMatrix_bounds f hR hj hA hD F θ).2.comp (goeMatrix_L2_lipschitz (j/n))
      apply hh.weaken
      change (L:ℝ)*sqrt (2*(j/n)) ≤ (Real.toNNReal (H/sqrt n):ℝ)
      rw [Real.coe_toNNReal _ (by positivity),hsqrt]
      calc
        _ = ((L:ℝ)*sqrt (2*j))/sqrt n := by ring
        _ ≤ H/sqrt n := div_le_div_of_nonneg_right hHL (sqrt_nonneg _)
    have hi (k : ℕ) (θ η : WordParameter m (Fin n)) (hθη : dist θ η ≤ 2*(1/4:ℝ)^k) :
        LipschitzWith (Real.toNNReal (H*(1/2:ℝ)^k/sqrt n)) (fun x=>T θ x-T η x) := by
      have hh := (generalTemplateMatrix_increments f hR hj hA hD F θ η).2.comp (goeMatrix_L2_lipschitz (j/n))
      apply hh.weaken
      change (((wordMixedCoeff B F.length:ℝ)*(generalTemplateHolder f R j A D*sqrt (dist θ η)))*sqrt (2*(j/n))) ≤
        (Real.toNNReal (H*(1/2:ℝ)^k/sqrt n):ℝ)
      rw [Real.coe_toNNReal _ (by positivity),hsqrt]
      have he : (wordMixedCoeff B F.length:ℝ)*(generalTemplateHolder f R j A D*sqrt (dist θ η))=
          (V:ℝ)*sqrt (dist θ η) := by
        change (wordMixedCoeff B F.length:ℝ)*(generalTemplateHolder f R j A D*sqrt (dist θ η)) =
          ((wordMixedCoeff B F.length:ℝ)*generalTemplateHolder f R j A D)*sqrt (dist θ η)
        ring
      rw [he]
      calc
        _ ≤ (V:ℝ)*(2*(1/2:ℝ)^k)*(sqrt (2*j)/sqrt n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sqrt_mesh_increment dist_nonneg k hθη) V.coe_nonneg) (by positivity)
        _ = (2*(V:ℝ)*sqrt (2*j))*(1/2:ℝ)^k/sqrt n := by ring
        _ ≤ H*(1/2:ℝ)^k/sqrt n := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hHV (by positivity)) (sqrt_nonneg _)
    exact gaussianMatrix_box_chaining hn hH hE hdim T hT hi
      (fun g=>generalTemplateGaussian_centered_continuous f hR hj hA hD F (j/n) (WithLp.toLp 2 g)) p
end SKGap
end
end

end OAI
