import Mathlib
import OAI.Probability.SKGap.Localization.PlantedFixedTime

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators

def rootBad {n : ℕ} (j A ε c ρ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : Prop :=
  ∃ y : Field n,vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ) ∧
    ∃ a : Field n,(∀ i,a i∈Icc 0 A) ∧
      (∑ i,(a i-spinVariance y i)^2) ≤ ε^2*(n:ℝ) ∧
      ∃ x : EuclideanSpace ℝ (Fin n),‖x‖=1 ∧ quadraticForm (fieldHessian j J y a) x.ofLp ≤ c

lemma rootBad_diagonal_transfer {n : ℕ} {j A ε c ρ δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h d : Field n) (hd : ∀ i,|d i| ≤ δ) :
    rootBad j A ε c ρ J h → rootBad j A ε (c+A*δ) (ρ+δ) (J+diagonal d) h := by
  rintro ⟨y,hy,a,ha,hdist,x,hx,hq⟩
  refine ⟨y,?_,a,ha,hdist,x,hx,?_⟩
  · have hdiff := tapField_diagonal_difference_bound hδ j J h y d hd
    have hh := vectorNorm_add_le (tapField j J h y)
      (tapField j (J+diagonal d) h y-tapField j J h y)
    rw [add_sub_cancel] at hh
    exact (hh.trans (add_le_add hy hdiff)).trans_eq (by ring)
  · have hdiff := hessian_diagonal_difference_bound hA hδ j J y a d x.ofLp
      (fun i=>(ha i).1) (fun i=>(ha i).2) hd
    have hv : vectorSqNorm x.ofLp=1 := by
      rw [← vectorNorm_sq]
      change ‖x‖^2=1
      rw [hx];norm_num
    rw [hv,mul_one] at hdiff
    linarith only [le_abs_self (quadraticForm (fieldHessian j (J+diagonal d) y a) x.ofLp-
      quadraticForm (fieldHessian j J y a) x.ofLp),hdiff,hq]

lemma rootBad_mono {n : ℕ} {j A ε c c' ρ ρ' : ℝ}
    (hc : c ≤ c') (hρ : ρ ≤ ρ') (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    rootBad j A ε c ρ J h → rootBad j A ε c' ρ' J h := by
  rintro ⟨y,hy,a,ha,hd,x,hx,hq⟩
  exact ⟨y,hy.trans (mul_le_mul_of_nonneg_right hρ (sqrt_nonneg _)),a,ha,hd,x,hx,hq.trans hc⟩

def eraseDiagonal {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  J-diagonal (fun i=>J i i)

lemma eraseDiagonal_add {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) :
    eraseDiagonal J+diagonal (fun i=>J i i)=J := sub_add_cancel _ _

lemma eraseDiagonal_diag {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    eraseDiagonal J i i=0 := by simp [eraseDiagonal]

lemma erased_planted_witness {n : ℕ} {j A K ε c ρ δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδρ : δ ≤ ρ/2) (hδc : A*δ ≤ c/2)
    (t : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) (b : Field n)
    (hd : ∀ i,|plantedInteraction j (goeMatrix (j/(n:ℝ)) g) i i| ≤ δ)
    (hJ : ∀ z : Field n,vectorNorm ((eraseDiagonal (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)))*ᵥz) ≤
      (K-δ)*vectorNorm z)
    (hbad : rootBad j A ε (c/2) (ρ/2)
      (eraseDiagonal (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))) (fun i=>t+b i)) :
    (g,b)∈plantedRootBad n j A K ε c ρ t := by
  let J := plantedInteraction j (goeMatrix (j/(n:ℝ)) g)
  have hjnorm := mulvec_add_diagonal_bound hδ (eraseDiagonal J) (fun i=>J i i) hJ hd
  rw [eraseDiagonal_add] at hjnorm
  have hjnorm' : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z := by
    simpa only [sub_add_cancel] using hjnorm
  have hh := rootBad_diagonal_transfer hA hδ (eraseDiagonal J) (fun i=>t+b i) (fun i=>J i i) hd hbad
  rw [eraseDiagonal_add] at hh
  obtain ⟨y,hy,a,ha,hdist,x,hx,hq⟩ := rootBad_mono (by linarith : c/2+A*δ ≤ c)
    (by linarith : ρ/2+δ ≤ ρ) J (fun i=>t+b i) hh
  exact ⟨hjnorm',y,hy,a,ha,hdist,x,hx,hq⟩
end SKGap
end
end

end OAI
