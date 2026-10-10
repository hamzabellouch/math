import Mathlib
import OAI.Probability.SKGap.Stability.WordStableAgreement
import OAI.Probability.SKGap.Matrix.GOEDiagonalSquare

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem zeroDiag_exact_word_simultaneous_prediction {j A D c : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (hc : 0<c) (L : ℕ) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧ ∀ n,N≤n → ∀ p : Bool,
      (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | opNorm (removeDiagonal (goeMatrix (j/n) g))≤2*sqrt j+1+1 ∧
        ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
          (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
          c≤ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a 1
            ((j/(n:ℝ))*∑ b,a b) (removeDiagonal (goeMatrix (j/n) g)))) ∧
          C< matrixWordSeminorm p
            (exactWord j a F (removeDiagonal (goeMatrix (j/n) g))-Matrix.diagonal (wordPrediction j a 1 F))} ≤
      (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
        ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2))) := by
  let R := 2*sqrt j+1+1
  let lo := min c ((1-sqrt j*A)^2/4)
  let hi := 2+A*(R+j*A)
  have hR : 0≤R := by dsimp [R];positivity
  have hint := path_interval hj.le hA.le hs
  have hlo : 0<lo := lt_min hc hint.1
  have hhi : 2+A*(2*sqrt j+1+j*A)≤hi := by dsimp [hi,R];nlinarith
  have hlohi : lo≤hi := (min_le_right _ _).trans (hint.2.trans hhi)
  obtain ⟨f,hf,_⟩ := exists_schwartz_inverse hlo hlohi
  have hfb : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹ := by
    intro x hx
    exact hf x ⟨(min_le_right _ _).trans hx.1,hx.2.trans hhi⟩
  obtain ⟨C,N,hC,hN,ht⟩ := actual_word_simultaneous_zerodiag_of_cutoff hj hA hs hD hAD L f hfb hR
  refine ⟨C,N,hC,hN,?_⟩
  intro n hn p
  have hn0 : 0<n := hN.trans_le hn
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  apply (measure_mono ?_).trans (ht n hn p)
  intro g hg
  obtain ⟨hMR,a,F,ha,hFL,hF,hFI,hstable,hbad⟩ := hg
  refine ⟨a,F,ha,hFL,hF,hFI,?_⟩
  have haq : ∀ i,0≤a i := fun i=>(ha i).1
  have haA : ∀ i,a i≤A := fun i=>(ha i).2
  have hq := diagonal_mean_bounds hj.le haq haA
  simp only [Fintype.card_fin] at hq
  have hb := stabilityMatrix_opNorm haq haA hA.le (show (1:ℝ)∈Icc 0 1 from ⟨zero_le_one,le_rfl⟩) hq.1 hMR
  have hnrm : opNorm (stabilityMatrix a 1 ((j/(n:ℝ))*∑ b,a b) (removeDiagonal (goeMatrix (j/n) g)))≤hi := by
    apply hb.trans
    dsimp [hi,R]
    nlinarith
  have hu : -hi≤ComplexSpectral.lowerRayleigh (-liftMatrix (stabilityMatrix a 1
      ((j/(n:ℝ))*∑ b,a b) (removeDiagonal (goeMatrix (j/n) g)))) :=
    (neg_le_neg hnrm).trans (lowerRayleigh_neg_lift_ge _)
  have hl : lo≤ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a 1
      ((j/(n:ℝ))*∑ b,a b) (removeDiagonal (goeMatrix (j/n) g)))) := (min_le_left _ _).trans hstable
  rw [stabilityMatrix_path_rep a haq zero_le_one] at hl hu
  have he := actualWord_agrees f hlo hf hR j haq (removeDiagonal (goeMatrix (j/n) g))
    (by simp [removeDiagonal,Matrix.transpose_sub,goeMatrix_transpose]) hMR (by simpa only [Fintype.card_fin] using hl)
      (by simpa only [Fintype.card_fin] using hu) F
  rwa [he]
end SKGap
end
end

end OAI
