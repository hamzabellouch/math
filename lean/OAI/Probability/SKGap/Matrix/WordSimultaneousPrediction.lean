import Mathlib
import OAI.Probability.SKGap.Matrix.WordBiasInduction
import OAI.Probability.SKGap.Stability.WordMeanSeminorm

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem actual_word_simultaneous_prediction {j A D : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (L : ℕ) :
    ∃ (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0≤R) (C : ℝ) (N : ℕ),
      R=2*sqrt j+1+1 ∧
      (∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹) ∧
      (∀ x,star (f x)=f x) ∧ 0<C ∧ 0<N ∧
      ∀ n,N≤n → ∀ p : Bool,
        (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
          (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
          C< matrixWordSeminorm p
            (actualWord f R hR j a 1 F (goeMatrix (j/n) g)-Matrix.diagonal (wordPrediction j a 1 F))} ≤
          (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  obtain ⟨f,R,hR,Cb,N,hRval,hf,hfr,hCb,hN,hbias⟩ := actual_word_uniform_bias hj hA hs hD hAD L
  obtain ⟨C0,hC0,hchain⟩ := all_actualWords_gaussian_chaining f hR hj.le hA (lt_of_lt_of_le zero_lt_one hD) L
  refine ⟨f,R,hR,C0+Cb,N,hRval,hf,hfr,by positivity,hN,?_⟩
  intro n hn p
  have hn0 : 1≤n := (Nat.succ_le_iff.mpr hN).trans hn
  apply (measure_mono ?_).trans (hchain n hn0 p)
  intro g hg
  obtain ⟨a,F,ha,hFL,hF,hFI,hg⟩ := hg
  refine ⟨a,F,ha,hFL,hF,?_⟩
  have hb : matrixWordSeminorm p (Matrix.diagonal (fun i=>wordExpected f hR j a 1 F i-wordPrediction j a 1 F i))≤Cb := by
    cases p with
    | false =>
      exact diagonalSeminorm_diagonal_bound hn0 hCb.le
        (hbias n hn a (fun i=>(ha i).1) (fun i=>(ha i).2) 1 ⟨zero_le_one,le_rfl⟩ F hFL hF hFI)
    | true =>
      change offDiagonalSeminorm (Matrix.diagonal _)≤Cb
      rw [offDiagonalSeminorm_diagonal]
      exact hCb.le
  have hdecomp := actualWord_diagonal_prediction_decompose (j:=j) f hR a 1 F g
  simp only [Fintype.card_fin] at hdecomp
  rw [hdecomp] at hg
  have hh := matrixWordSeminorm_add p
    (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
      actualWord f R hR j a 1 F (goeMatrix (j/n) x)) (WithLp.toLp 2 g))
    (Matrix.diagonal (fun i=>wordExpected f hR j a 1 F i-wordPrediction j a 1 F i))
  linarith
end SKGap
end
end

end OAI
