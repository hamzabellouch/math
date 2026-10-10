import Mathlib
import OAI.Analysis.MatrixSigning.Potential.NegativeWeight
import OAI.Analysis.MatrixSigning.Matrices.DerivInvHPath

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma stationary_pairing (X Y P Q U V : H d) (η : H d →L[ℝ] H d)
    (hη : SymmetricMap η) (ε : ℝ)
    (hP : sandwich (invH X) P = η Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = η P + ε • (Hermitian.one : H d)) :
    inner ℝ P (sandwich (invH X) U - η V) +
      inner ℝ Q (sandwich (invH Y) V - η U) = ε * Hermitian.realTrace (U+V) := by
  rw [inner_sub_right, inner_sub_right, inner_sandwich, inner_sandwich, hP, hQ]
  rw [inner_add_left, inner_add_left, inner_smul_leftH, inner_smul_leftH,
    inner_one, inner_one]
  rw [hη Q U, hη P V]
  simp only [realTrace_add]
  ring

lemma objective_variation_pairing (X Y P Q U V S' : H d)
    (η η' : H d →L[ℝ] H d) (hη : SymmetricMap η) (ε t' : ℝ)
    (hP : sandwich (invH X) P = η Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = η P + ε • (Hermitian.one : H d))
    (htr : Hermitian.realTrace P + Hermitian.realTrace Q = 1)
    (hx : sandwich (invH X) U - η V + t' • (Hermitian.one : H d) = S' + η' Y)
    (hy : sandwich (invH Y) V - η U + t' • (Hermitian.one : H d) = -S' + η' X) :
    t' + ε * Hermitian.realTrace (U+V) = inner ℝ P (S' + η' Y) + inner ℝ Q (-S' + η' X) := by
  rw [← hx, ← hy, inner_add_right, inner_add_right, inner_smul_rightH,
    inner_smul_rightH, inner_one', inner_one']
  have h := stationary_pairing X Y P Q U V η hη ε hP hQ
  linear_combination -h - t' * htr

end CurrentKS.Variational

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma inner_eta₁ (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (P Y : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) :
    inner ℝ P (eta₁ c A x h Y) =
      ∑ i, c*psi₁ (x i)*h i*inner ℝ (A i) Y*inner ℝ (A i) P := by
  rw [eta₁_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) Y (hA i) (hrank i),
    real_inner_smul_right P _ (c*psi₁ (x i)*h i),
    real_inner_smul_right P (A i) (inner ℝ (A i) Y),real_inner_comm P (A i)]
  ring

lemma inner_eta₂ (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (P Y : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) :
    inner ℝ P (eta₂ c A x h Y) =
      ∑ i, -c*kappa (x i)*(h i)^2*inner ℝ (A i) Y*inner ℝ (A i) P := by
  rw [eta₂_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) Y (hA i) (hrank i),
    real_inner_smul_right P _ (-c*kappa (x i)*(h i)^2),
    real_inner_smul_right P (A i) (inner ℝ (A i) Y),real_inner_comm P (A i)]
  ring

lemma first_input_pairing (c : ℝ) (A : Fin N → H d) (x h : Coordinates N) (X Y P Q : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) :
    inner ℝ P (S A h + eta₁ c A x h Y) + inner ℝ Q (-S A h + eta₁ c A x h X) =
      ∑ i, h i*((1+c*psi₁ (x i)*inner ℝ (A i) Y)*inner ℝ (A i) P -
        (1-c*psi₁ (x i)*inner ℝ (A i) X)*inner ℝ (A i) Q) := by
  rw [inner_add_right,inner_add_right,inner_neg_right,inner_eta₁ c A x h P Y hA hrank,
    inner_eta₁ c A x h Q X hA hrank]
  simp only [S,inner_sum]
  rw [← Finset.sum_neg_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right P (A i) (h i),real_inner_smul_right Q (A i) (h i),
    real_inner_comm P (A i),real_inner_comm Q (A i)]
  ring

lemma second_input_pairing (c : ℝ) (A : Fin N → H d) (x h : Coordinates N)
    (X Y P Q U V : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) :
    inner ℝ P (jordanCLM (invH X) (sandwich (invH X) U) U +
        (2 : ℝ) • eta₁ c A x h V + eta₂ c A x h Y) +
      inner ℝ Q (jordanCLM (invH Y) (sandwich (invH Y) V) V +
        (2 : ℝ) • eta₁ c A x h U + eta₂ c A x h X) =
      2*energy X Y P Q U V + mixedTerm c A x h P Q U V - c*negativeWeight A x h X Y P Q := by
  rw [jordan_inverse_square,jordan_inverse_square]
  simp only [inner_add_right]
  rw [real_inner_smul_right P _ (2 : ℝ),real_inner_smul_right P _ (2 : ℝ),
    real_inner_smul_right Q _ (2 : ℝ),real_inner_smul_right Q _ (2 : ℝ)]
  rw [inner_eta₁ c A x h P V hA hrank,inner_eta₁ c A x h Q U hA hrank,
    inner_eta₂ c A x h P Y hA hrank,inner_eta₂ c A x h Q X hA hrank]
  have he : 2*(∑ i, c*psi₁ (x i)*h i*inner ℝ (A i) V*inner ℝ (A i) P) +
      2*(∑ i, c*psi₁ (x i)*h i*inner ℝ (A i) U*inner ℝ (A i) Q) +
      (∑ i, -c*kappa (x i)*(h i)^2*inner ℝ (A i) Y*inner ℝ (A i) P) +
      (∑ i, -c*kappa (x i)*(h i)^2*inner ℝ (A i) X*inner ℝ (A i) Q) =
      mixedTerm c A x h P Q U V - c*negativeWeight A x h X Y P Q := by
    unfold mixedTerm negativeWeight
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change _ = 2*(inner ℝ P (sandwich (invH X) (sandwich U (invH X))) +
    inner ℝ Q (sandwich (invH Y) (sandwich V (invH Y)))) + _ - _
  linarith

end CurrentKS.State

end

end OAI
