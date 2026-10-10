import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Coordinates
import OAI.Analysis.MatrixSigning.Matrices.SandwichShiftInverse

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma eta_rank_one (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (Z : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) :
    eta c A x Z = ∑ i, (c*psi (x i)*inner ℝ (A i) Z) • A i := by
  rw [eta_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) Z (hA i) (hrank i),smul_smul]

lemma inner_eta_rank_one (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (Z W : H d)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1) :
    inner ℝ (eta c A x Z) W =
      ∑ i, c*psi (x i)*inner ℝ (A i) Z*inner ℝ (A i) W := by
  rw [eta_rank_one c A x Z hA hrank,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_smul_left (A i) W (c*psi (x i)*inner ℝ (A i) Z)

def energy (X Y P Q U V : H d) : ℝ :=
  inner ℝ P (sandwich (invH X) (sandwich U (invH X))) +
  inner ℝ Q (sandwich (invH Y) (sandwich V (invH Y)))

lemma energy_nonneg (X Y P Q U V : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d)
    (hP : P ∈ psdCone d) (hQ : Q ∈ psdCone d) : 0 ≤ energy X Y P Q U V := by
  exact add_nonneg (inner_nonneg_of_psd _ _ hP (sandwich_psd _ _ (sandwich_psd _ _ hX.inv.posSemidef)))
    (inner_nonneg_of_psd _ _ hQ (sandwich_psd _ _ (sandwich_psd _ _ hY.inv.posSemidef)))

lemma energy_stationary_bound (c ε : ℝ) (hε : 0 ≤ ε) (A : Fin N → H d) (x : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (X Y P Q U V : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d)
    (hP : sandwich (invH X) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = eta c A x P + ε • (Hermitian.one : H d)) :
    (∑ i, c*psi (x i)*(inner ℝ (A i) Q * inner ℝ (A i) (sandwich U (invH X)) +
      inner ℝ (A i) P * inner ℝ (A i) (sandwich V (invH Y)))) ≤ energy X Y P Q U V := by
  unfold energy
  rw [inner_sandwich (invH X) _ P, inner_sandwich (invH Y) _ Q,hP,hQ,inner_add_left,inner_add_left,
    real_inner_smul_left (Hermitian.one : H d) (sandwich U (invH X)) ε,
    real_inner_smul_left (Hermitian.one : H d) (sandwich V (invH Y)) ε,inner_one,inner_one,
    inner_eta_rank_one c A x Q _ hA hrank,inner_eta_rank_one c A x P _ hA hrank]
  have h₁ := mul_nonneg hε (realTrace_nonneg (sandwich_psd U (invH X) hX.inv.posSemidef))
  have h₂ := mul_nonneg hε (realTrace_nonneg (sandwich_psd V (invH Y) hY.inv.posSemidef))
  have he : (∑ i, c*psi (x i)*(inner ℝ (A i) Q * inner ℝ (A i) (sandwich U (invH X)) +
      inner ℝ (A i) P * inner ℝ (A i) (sandwich V (invH Y)))) =
      (∑ i, c*psi (x i)*inner ℝ (A i) Q * inner ℝ (A i) (sandwich U (invH X))) +
      (∑ i, c*psi (x i)*inner ℝ (A i) P * inner ℝ (A i) (sandwich V (invH Y))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  linarith

end
end CurrentKS.State

end OAI
