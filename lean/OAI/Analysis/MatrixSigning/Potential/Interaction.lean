import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Energy
import OAI.Analysis.MatrixSigning.Matrices.InnerMonoRightPsd

namespace OAI

open Matrix

namespace CurrentKS.Interaction
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.State Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def interaction (c : ℝ) (A : Fin N → H d) (l : Fin N → ℝ) (X : H d) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => c*l i*l j*inner ℝ (A i) (sandwich X (A j))

def responseInput (A : Fin N → H d) (l F : Fin N → ℝ) : H d :=
  ∑ i, (l i*F i) • A i

lemma interaction_symm (c : ℝ) (A : Fin N → H d) (l : Fin N → ℝ) (X : H d) :
    (interaction c A l X).IsHermitian := by
  ext i j
  change c*l j*l i*inner ℝ (A j) (sandwich X (A i)) = c*l i*l j*inner ℝ (A i) (sandwich X (A j))
  rw [inner_sandwich,real_inner_comm (sandwich X (A j)) (A i)]
  ring

lemma interaction_nonneg {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hA : ∀ i, A i ∈ psdCone d) (l : Fin N → ℝ) (hl : ∀ i, 0 ≤ l i) (X : H d) (i j : Fin N) :
    0 ≤ interaction c A l X i j := by
  exact mul_nonneg (mul_nonneg (mul_nonneg hc (hl i)) (hl j))
    (inner_nonneg_of_psd _ _ (hA i) (sandwich_psd _ _ (hA j)))

lemma sandwich_responseInput (A : Fin N → H d) (l F : Fin N → ℝ) (X : H d) :
    sandwich X (responseInput A l F) = ∑ i, (l i*F i) • sandwich X (A i) := by
  change sandwichCLM X (∑ i, (l i*F i) • A i) = _
  simp only [map_sum,map_smul,sandwichCLM_apply]

lemma interaction_mulVec (c : ℝ) (A : Fin N → H d) (l F : Fin N → ℝ) (X : H d) (i : Fin N) :
    (interaction c A l X *ᵥ F) i = c*l i*inner ℝ (A i) (sandwich X (responseInput A l F)) := by
  rw [sandwich_responseInput,inner_sum]
  simp only [Matrix.mulVec,dotProduct,interaction,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_smul_right (A i) (sandwich X (A j)) (l j*F j)]
  ring

lemma interaction_diag (c : ℝ) (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (hrank : ∀ i, (A i : Mat d).rank ≤ 1) (l : Fin N → ℝ) (X : H d) (i : Fin N) :
    interaction c A l X i i = c*(l i*inner ℝ (A i) X)^2 := by
  unfold interaction
  rw [inner_eq_trace]
  change c*l i*l i*((A i : Mat d)*((X : Mat d)*(A i : Mat d)*(X : Mat d))).trace.re = _
  rw [← mul_assoc,← mul_assoc,CurrentKS.rank_one_sandwich _ (hA i) (hrank i)]
  rw [Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,Complex.mul_re]
  have him : (((A i : Mat d)*(X : Mat d)).trace).im = 0 := by
    have he := trace_mul_real (A i) X
    exact congrArg Complex.im he |>.symm
  rw [him,mul_zero,sub_zero]
  rw [inner_eq_trace]
  ring

lemma interaction_quad (c : ℝ) (A : Fin N → H d) (l F : Fin N → ℝ) (X : H d) :
    F ⬝ᵥ (interaction c A l X *ᵥ F) =
      c*inner ℝ (responseInput A l F) (sandwich X (responseInput A l F)) := by
  simp only [dotProduct,interaction_mulVec]
  have he (Z : H d) : inner ℝ (responseInput A l F) Z =
      ∑ i, (l i*F i)*inner ℝ (A i) Z := by
    rw [responseInput,sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    exact real_inner_smul_left (A i) Z (l i*F i)
  rw [he]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma interaction_psd {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) (l : Fin N → ℝ)
    (X : H d) (hX : X ∈ psdCone d) : (interaction c A l X).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨interaction_symm c A l X,fun F => ?_⟩
  simp only [star_trivial,interaction_quad]
  exact mul_nonneg hc (sandwich_inner_nonneg X _ hX)

lemma interaction_entry_bound {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hA : ∀ i, A i ∈ psdCone d) (l : Fin N → ℝ) (hl : ∀ i, 0 ≤ l i)
    (X : H d) (hX : X ∈ psdCone d) (i j : Fin N) :
    interaction c A l X i j ≤ c*(l i*inner ℝ (A i) X)*(l j*inner ℝ (A j) X) := by
  have hh := mul_le_mul_of_nonneg_left (inner_sandwich_le X (A i) (A j) hX (hA i) (hA j))
    (mul_nonneg (mul_nonneg hc (hl i)) (hl j))
  change c*l i*l j*inner ℝ (A i) (sandwich X (A j)) ≤ _
  convert hh using 1
  first | rfl | ring

lemma interaction_entry_square {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hA : ∀ i, A i ∈ psdCone d) (l : Fin N → ℝ) (hl : ∀ i, 0 ≤ l i)
    (X : H d) (hX : X ∈ psdCone d) (i j : Fin N) :
    (interaction c A l X i j)^2 ≤ c*(l i*inner ℝ (A i) X)*(l j*inner ℝ (A j) X)*interaction c A l X i j := by
  have hh := mul_le_mul_of_nonneg_right (interaction_entry_bound hc A hA l hl X hX i j)
    (interaction_nonneg hc A hA l hl X i j)
  simpa only [pow_two] using hh

lemma eta_response (c : ℝ) (A : Fin N → H d) (x : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (l m G : Fin N → ℝ) (hlm : ∀ i, l i*m i = psi (x i)) (Y : H d) :
    eta c A x (sandwich Y (responseInput A m G)) =
      responseInput A l (interaction c A m Y *ᵥ G) := by
  rw [eta_rank_one c A x _ hA hrank]
  unfold responseInput
  apply Finset.sum_congr rfl
  intro i _
  rw [interaction_mulVec,← hlm i]
  congr 1
  change c*(l i*m i)*inner ℝ (A i) (sandwich Y (responseInput A m G)) = _
  ring

lemma eta_as_response (c : ℝ) (A : Fin N → H d) (x : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (l m : Fin N → ℝ) (hlm : ∀ i, l i*m i = psi (x i)) (Q : H d) :
    eta c A x Q = c • responseInput A l (fun i => m i*inner ℝ (A i) Q) := by
  rw [eta_rank_one c A x Q hA hrank]
  simp only [responseInput,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hlm i]
  congr 1
  ring

lemma sandwich_one_square (X : H d) :
    ((sandwich X one : H d) : Mat d) = (X : Mat d)*(X : Mat d) := by
  change (X : Mat d)*1*(X : Mat d) = _
  rw [mul_one]

lemma interaction_duality (c ε : ℝ) (A : Fin N → H d) (x : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (l m : Fin N → ℝ) (hlm : ∀ i, l i*m i = psi (x i))
    (X P Q : H d) (hX : X ∈ pd d)
    (hP : sandwich (invH X) P = eta c A x Q + ε • (Hermitian.one : H d)) (i : Fin N) :
    (interaction c A l X *ᵥ (fun j => m j*inner ℝ (A j) Q)) i =
      l i*inner ℝ (A i) P - ε*l i*inner ℝ (A i) (sandwich X one) := by
  have hp := congrArg (sandwichCLM X) hP
  change sandwich X (sandwich (invH X) P) = sandwichCLM X (eta c A x Q + ε • (Hermitian.one : H d)) at hp
  rw [sandwich_inverse_left X P hX,map_add,map_smul,eta_as_response c A x hA hrank l m hlm Q,
    map_smul] at hp
  change P = c • sandwich X (responseInput A l (fun j => m j*inner ℝ (A j) Q)) +
      ε • sandwich X one at hp
  rw [interaction_mulVec,hp,inner_add_right,
    real_inner_smul_right (A i) _ c,real_inner_smul_right (A i) _ ε]
  ring

end
end CurrentKS.Interaction

end OAI
