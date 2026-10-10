import Mathlib
import OAI.Analysis.MatrixSigning.Potential.ValueFeasible
import OAI.Analysis.MatrixSigning.Matrices.SandwichShiftInverse

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma sum_update_composite {α β : Type*} [AddCommGroup β] (f : Fin N → α → β)
    (x : Fin N → α) (i : Fin N) (a : α) :
    (∑ j, f j (Function.update x i a j)) = (∑ j, f j (x j))+f i a-f i (x i) := by
  simp only [Function.apply_update]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have he := Finset.sum_erase_add Finset.univ (fun j => f j (x j)) (Finset.mem_univ i)
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← he]
  abel

lemma S_update (A : Fin N → H d) (x : Coordinates N) (i : Fin N) (t : ℝ) :
    S A (Function.update x i t) = S A x+(t-x i) • A i := by
  rw [S,sum_update_composite (fun (j : Fin N) (r : ℝ) => r • A j) x i t]
  simp only [S]
  module

lemma eta_update (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (i : Fin N) (t : ℝ) (Z : H d) :
    eta c A (Function.update x i t) Z = eta c A x Z+(c*(psi t-psi (x i))) • sandwich (A i) Z := by
  rw [eta_apply,sum_update_composite (fun (j : Fin N) (r : ℝ) => (c*psi r) • sandwich (A j) Z) x i t,eta_apply]
  module

lemma psi_endpoint {t : ℝ} (ht : |t| = 1) : psi t = 0 := by
  have hh : t^2 = 1 := by nlinarith [sq_abs t]
  simp [psi,hh]

lemma Cube_update {x : Coordinates N} (hx : Cube x) (i : Fin N) {t : ℝ} (ht : |t| ≤ 1) :
    Cube (Function.update x i t) := by
  intro j
  by_cases hj : j=i
  · subst j; simpa using ht
  · simpa [Function.update_of_ne hj] using hx j

lemma endpoint_feasible {c : ℝ} (A : Fin N → H d) (x : Coordinates N) (i : Fin N) {t : ℝ}
    (ht : |t| = 1) (hA : A i ∈ psdCone d) (hrank : (A i : Mat d).rank ≤ 1)
    (z : Point d) (hz : z ∈ feasible (S A x) (eta c A x))
    (hplus : t-x i ≤ c*psi (x i)*inner ℝ (A i) z.2.2)
    (hminus : x i-t ≤ c*psi (x i)*inner ℝ (A i) z.2.1) :
    z ∈ feasible (S A (Function.update x i t)) (eta c A (Function.update x i t)) := by
  have hz := (feasible_iff (S A x) (eta c A x) z).mp hz
  apply (feasible_iff (S A (Function.update x i t))
    (eta c A (Function.update x i t)) z).mpr
  refine ⟨hz.1,hz.2.1,?_,?_⟩
  · have he : invH z.2.1+S A (Function.update x i t)+eta c A (Function.update x i t) z.2.2 =
        invH z.2.1+S A x+eta c A x z.2.2 +
          (t-x i-c*psi (x i)*inner ℝ (A i) z.2.2) • A i := by
      rw [S_update,eta_update,psi_endpoint ht,zero_sub,mul_neg,
        sandwich_rank_one (A i) z.2.2 hA hrank]
      module
    apply he.le.trans
    have hs : (t-x i-c*psi (x i)*inner ℝ (A i) z.2.2) • A i ≤ 0 := by
      simpa only [zero_smul] using scalar_mono_psd hA (sub_nonpos.mpr hplus)
    calc
      _ ≤ invH z.2.1+S A x+eta c A x z.2.2 := by
        simpa only [add_zero] using add_le_add (le_refl (invH z.2.1+S A x+eta c A x z.2.2)) hs
      _ ≤ _ := hz.2.2.1
  · have he : invH z.2.2-S A (Function.update x i t)+eta c A (Function.update x i t) z.2.1 =
        invH z.2.2-S A x+eta c A x z.2.1 +
          (x i-t-c*psi (x i)*inner ℝ (A i) z.2.1) • A i := by
      rw [S_update,eta_update,psi_endpoint ht,zero_sub,mul_neg,
        sandwich_rank_one (A i) z.2.1 hA hrank]
      module
    apply he.le.trans
    have hs : (x i-t-c*psi (x i)*inner ℝ (A i) z.2.1) • A i ≤ 0 := by
      simpa only [zero_smul] using scalar_mono_psd hA (sub_nonpos.mpr hminus)
    calc
      _ ≤ invH z.2.2-S A x+eta c A x z.2.1 := by
        simpa only [add_zero] using add_le_add (le_refl (invH z.2.2-S A x+eta c A x z.2.1)) hs
      _ ≤ _ := hz.2.2.2

def potential (c ε lam : ℝ) (A : Fin N → H d) (x : Coordinates N) : ℝ :=
  value ε (S A x) (eta c A x)+lam*∑ i,psi (x i)

lemma endpoint_potential_le [NeZero d] {c ε lam : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x : Coordinates N) (hx : Cube x) (i : Fin N) {t : ℝ}
    (ht : |t| = 1) (hA : A i ∈ psdCone d) (hrank : (A i : Mat d).rank ≤ 1)
    (z : Point d) (hz : z ∈ feasible (S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S A x) (eta c A x), objective ε z ≤ objective ε w)
    (hplus : t-x i ≤ c*psi (x i)*inner ℝ (A i) z.2.2)
    (hminus : x i-t ≤ c*psi (x i)*inner ℝ (A i) z.2.1) :
    potential c ε lam A (Function.update x i t) ≤ potential c ε lam A x-lam*psi (x i) := by
  have hf := endpoint_feasible A x i ht hA hrank z hz hplus hminus
  have hv := value_le_feasible ε hε _ _ (eta_positive hc A (Cube_update hx i ht.le)) z hf
  rw [← value_eq_of_min ε _ _ z hz hmin] at hv
  rw [potential,potential,sum_update_composite (fun (_ : Fin N) (r : ℝ) => psi r) x i t,psi_endpoint ht,add_zero]
  nlinarith

end
end CurrentKS.State

end OAI
