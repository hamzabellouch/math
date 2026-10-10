import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Pair
import OAI.Analysis.MatrixSigning.Potential.NegativeWeight
import OAI.Analysis.MatrixSigning.Potential.Interaction

namespace OAI

open Matrix

namespace CurrentKS.Interaction
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.State Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma responseInput_sub (A : Fin N → H d) (l F G : Fin N → ℝ) :
    responseInput A l (F-G) = responseInput A l F-responseInput A l G := by
  unfold responseInput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (l i*(F i-G i)) • A i = (l i*F i) • A i-(l i*G i) • A i
  module

lemma responseInput_neg (A : Fin N → H d) (l F : Fin N → ℝ) :
    responseInput A l (-F) = -responseInput A l F := by
  unfold responseInput
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (l i*(-F i)) • A i = -((l i*F i) • A i)
  module

lemma first_rhs_rescaled (c : ℝ) (A : Fin N → H d) (x h Hh T l : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (Y : H d) (hl : ∀ i, l i*T i = 1+c*psi₁ (x i)*inner ℝ (A i) Y)
    (hHT : ∀ i, T i*h i = Hh i) :
    S A h+eta₁ c A x h Y = responseInput A l Hh := by
  rw [S,eta₁_apply,← Finset.sum_add_distrib,responseInput]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) Y (hA i) (hrank i),smul_smul,← add_smul]
  congr 1
  rw [← hHT i,← mul_assoc,hl i]
  ring

lemma second_rhs_rescaled (c : ℝ) (A : Fin N → H d) (x h Hh T m : Coordinates N)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (X : H d) (hm : ∀ i, m i*T i = 1-c*psi₁ (x i)*inner ℝ (A i) X)
    (hHT : ∀ i, T i*h i = Hh i) :
    -S A h+eta₁ c A x h X = -responseInput A m Hh := by
  rw [S,eta₁_apply,responseInput,← Finset.sum_neg_distrib,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) X (hA i) (hrank i),smul_smul]
  have he : -h i+c*psi₁ (x i)*h i*inner ℝ (A i) X = -(m i*Hh i) := by
    rw [← hHT i,← mul_assoc,hm i]
    ring
  calc
    _ = (-h i+c*psi₁ (x i)*h i*inner ℝ (A i) X) • A i := by module
    _ = (-(m i*Hh i)) • A i := congrArg (fun r : ℝ => r • A i) he
    _ = _ := by module

lemma identify_responses [NeZero d] {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (A : Fin N → H d) (x h Hh T l m F G : Coordinates N) (hx : Cube x)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (X Y P Q U V : H d) (hX : X ∈ pd d) (hY : Y ∈ pd d) (hPpos : P ∈ pd d) (hQpos : Q ∈ pd d)
    (hP : sandwich (invH X) P = eta c A x Q+ε • (Hermitian.one : H d))
    (hQ : sandwich (invH Y) Q = eta c A x P+ε • (Hermitian.one : H d))
    (hlm : ∀ i, l i*m i = psi (x i))
    (hl : ∀ i, l i*T i = 1+c*psi₁ (x i)*inner ℝ (A i) Y)
    (hm : ∀ i, m i*T i = 1-c*psi₁ (x i)*inner ℝ (A i) X)
    (hHT : ∀ i, T i*h i = Hh i)
    (hF : F-(interaction c A m Y *ᵥ G) = Hh)
    (hG : G-(interaction c A l X *ᵥ F) = -Hh)
    (hU : sandwich (invH X) U-eta c A x V = S A h+eta₁ c A x h Y)
    (hV : sandwich (invH Y) V-eta c A x U = -S A h+eta₁ c A x h X) :
    U = sandwich X (responseInput A l F) ∧ V = sandwich Y (responseInput A m G) := by
  have hPX : P = sandwich X (eta c A x Q)+ε • sandwich X (Hermitian.one : H d) := by
    rw [← sandwich_smul,← sandwich_add,← hP,sandwich_inverse_left X P hX]
  have hQY : Q = sandwich Y (eta c A x P)+ε • sandwich Y (Hermitian.one : H d) := by
    rw [← sandwich_smul,← sandwich_add,← hQ,sandwich_inverse_left Y Q hY]
  obtain ⟨W,hW,_⟩ := linConstraint_positive_inverse X Y P Q (eta c A x)
    (eta_positive hc A hx) hX hY hPpos hQpos hε hPX hQY
  have he : (U,V) = (sandwich X (responseInput A l F),sandwich Y (responseInput A m G)) := by
    apply W.injective
    rw [hW,hW,Variational.linConstraint_apply,Variational.linConstraint_apply]
    apply Prod.ext <;> dsimp only [Prod.fst, Prod.snd]
    · erw [hU,first_rhs_rescaled c A x h Hh T l hA hrank Y hl hHT,
        sandwich_inverse_right X _ hX,eta_response c A x hA hrank l m G hlm Y,
        ← responseInput_sub,hF]
    · erw [hV,second_rhs_rescaled c A x h Hh T m hA hrank X hm hHT,
        sandwich_inverse_right Y _ hY,eta_response c A x hA hrank m l F
          (fun i => (mul_comm (m i) (l i)).trans (hlm i)) X,← responseInput_sub,hG,responseInput_neg]
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

end
end CurrentKS.Interaction

end OAI
