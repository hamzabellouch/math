import OAI.NumberTheory.JointDickman.Probability.KernelDifferenceMoments
import OAI.NumberTheory.JointDickman.Counting.LagEnvelopeMoments

namespace OAI

/-! # A positive sampling envelope for the latent-minus-model error -/
namespace JointDickman
open Finset PublishedInputs

noncomputable def addLagEnvelope {M : ℕ} {A : Type*}
    (K : Fin M → Fin M → A → A → ℝ) (T : ℕ) (D : ℝ)
    (i k : Fin M) (a b : A) : ℝ := K i k a b+lagEnvelope T D i k

theorem addLagEnvelope_dominates {M T : ℕ} {A : Type*} {D : ℝ}
    (K J : Fin M → Fin M → A → A → ℝ)
    (hK : ∀ i k a b, 0 ≤ K i k a b)
    (hJ : ∀ i k a b, |J i k a b| ≤ lagEnvelope T D i k)
    (i k : Fin M) (a b : A) :
    |K i k a b-J i k a b| ≤ addLagEnvelope K T D i k a b := by
  exact (abs_sub _ _).trans (add_le_add
    (le_of_eq (abs_of_nonneg (hK i k a b))) (hJ i k a b))

theorem addLagEnvelope_moments {M T : ℕ} {A : Type*} [Fintype A]
    (hT : 0 < T) {D C q : ℝ} (hD : 0 ≤ D)
    (p : Fin M → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K J : Fin M → Fin M → A → A → ℝ)
    (hJ : ∀ i k a b, |J i k a b| ≤ lagEnvelope T D i k)
    (hrow : ∀ i a, |siteRowMean p K i a| ≤ C)
    (hquad : ∀ i, siteRowSquareMass p K i ≤ q) :
    (∀ i a, |siteRowMean p (addLagEnvelope K T D) i a| ≤ C+2*D*Real.exp 24) ∧
    (∀ i, siteRowSquareMass p (addLagEnvelope K T D) i ≤ q*2+4*D^2*Real.exp 1200/(T : ℝ)) ∧
    (∀ i, siteRowSquareMass p (fun i k a b => K i k a b-J i k a b) i ≤
      q*2+4*D^2*Real.exp 1200/(T : ℝ)) := by
  let F : Fin M → Fin M → A → A → ℝ := fun i k _ _ => lagEnvelope T D i k
  have hF (i k : Fin M) (a b : A) : |F i k a b| ≤ lagEnvelope T D i k := by
    dsimp only [F]
    rw [abs_of_nonneg (lagEnvelope_nonneg T hD i k)]
  have hFsq (i : Fin M) := lagEnvelope_row_square_mass hT hD p hp hpone F hF i
  have hJsq (i : Fin M) := lagEnvelope_row_square_mass hT hD p hp hpone J hJ i
  refine ⟨?_,?_,?_⟩
  · intro i a
    change |siteRowMean p (fun i k a b => K i k a b+F i k a b) i a| ≤ _
    rw [siteRowMean_add]
    exact (abs_add_le _ _).trans
      (add_le_add (hrow i a) (lagEnvelope_row_mean hT hD p hp hpone F hF i a))
  · intro i
    change siteRowSquareMass p (fun i k a b => K i k a b+F i k a b) i ≤ _
    have h := (siteRowSquareMass_add_le p hp K F i).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hquad i) (by norm_num))
        (mul_le_mul_of_nonneg_left (hFsq i) (by norm_num)))
    convert h using 1
    ring
  · intro i
    have h := (siteRowSquareMass_sub_le p hp K J i).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hquad i) (by norm_num))
        (mul_le_mul_of_nonneg_left (hJsq i) (by norm_num)))
    convert h using 1
    ring

end JointDickman

end OAI
