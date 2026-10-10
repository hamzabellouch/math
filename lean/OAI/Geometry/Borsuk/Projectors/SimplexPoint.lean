import Mathlib

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set
noncomputable def simplexPoint {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) : Fin (n+1) → ℝ :=
  Fin.cases (1 - ∑ i, z i) (fun i => z i)

def simplexInterior (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | (∀ i, 0 < z i) ∧ ∑ i, z i < 1}

lemma simplexInterior_isOpen (n : ℕ) : IsOpen (simplexInterior n) := by
  have h₁ : IsOpen {z : EuclideanSpace ℝ (Fin n) | ∀ i, 0 < z i} := by
    rw [show {z : EuclideanSpace ℝ (Fin n) | ∀ i, 0 < z i} =
      ⋂ i, {z : EuclideanSpace ℝ (Fin n) | 0 < z i} from by ext; simp]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (EuclideanSpace.proj i).continuous)
  exact h₁.inter (isOpen_lt (continuous_finsetSum Finset.univ
    (fun i _ => (EuclideanSpace.proj i).continuous)) continuous_const)

lemma simplexInterior_nonempty (n : ℕ) : (simplexInterior n).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)/(n+1)),?_,?_⟩
  · intro i
    change 0 < (1:ℝ)/(n+1)
    positivity
  · change ∑ _i : Fin n, (1:ℝ)/(n+1) < 1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [mul_one_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)

lemma simplexPoint_pos {n : ℕ} {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ simplexInterior n) :
    ∀ i, 0 < simplexPoint z i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact sub_pos.mpr hz.2
  · exact hz.1 j

lemma simplexPoint_sum {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) : ∑ i, simplexPoint z i = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [simplexPoint,Fin.cases_zero,Fin.cases_succ]
  ring

lemma simplexPoint_succ {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    simplexPoint z i.succ = z i := rfl
end BorsukNine

namespace BorsukNine
open Set
open scoped RealInnerProductSpace

end BorsukNine

end OAI
