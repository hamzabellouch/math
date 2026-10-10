import OAI.Analysis.MarkovType.TriangularBasic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TriangularSystem

def liftQuotient (F : Submodule ℝ X) [IsClosed (F : Set X)]
    {n : ℕ} {θ : ℝ} (s : TriangularSystem (X ⧸ F) n θ) :
    TriangularSystem X n (θ / 2) := by
  classical
  let q : X →L[ℝ] X ⧸ F := F.mkQ.mkContinuous 1
    (fun x => by simpa only [one_mul, Submodule.mkQ_apply] using Submodule.Quotient.norm_mk_le F x)
  have hq (x : X) : ‖q x‖ ≤ ‖x‖ := Submodule.Quotient.norm_mk_le F x
  have hrep (i : Fin n) : ∃ x : X, q x = s.vectors i ∧ ‖x‖ ≤ 2 := by
    obtain ⟨x, hx, hnorm⟩ :=
      Submodule.Quotient.norm_mk_lt (s.vectors i) (by norm_num : (0 : ℝ) < 1)
    refine ⟨x, hx, ?_⟩
    linarith [s.vectors_bound i]
  let x : Fin n → X := fun i => Classical.choose (hrep i)
  have hx (i : Fin n) : q (x i) = s.vectors i := (Classical.choose_spec (hrep i)).1
  have hnorm (i : Fin n) : ‖x i‖ ≤ 2 := (Classical.choose_spec (hrep i)).2
  refine {
    vectors := fun i => (1 / 2 : ℝ) • x i
    functionals := fun j => (s.functionals j).comp q
    vectors_bound := ?_
    functionals_bound := ?_
    pairing := ?_ }
  · intro i
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [hnorm i]
  · intro j
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖s.functionals j (q z)‖ ≤ 1 * ‖z‖
    calc
      ‖s.functionals j (q z)‖ ≤ ‖s.functionals j‖ * ‖q z‖ :=
        (s.functionals j).le_opNorm (q z)
      _ ≤ 1 * ‖q z‖ :=
        mul_le_mul_of_nonneg_right (s.functionals_bound j) (norm_nonneg _)
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_left (hq z) zero_le_one
  · intro i j
    change s.functionals j (q ((1 / 2 : ℝ) • x i)) = _
    rw [q.map_smul, hx, map_smul, s.pairing]
    by_cases hji : j ≤ i
    · simp only [ite_eq_left hji, smul_eq_mul]
      ring
    · simp only [ite_eq_right hji, smul_zero]

end TriangularSystem

theorem no_triangular_quotient_of_no_triangular
    {n : ℕ} {θ : ℝ} (hX : ¬ Nonempty (TriangularSystem X n (θ / 2)))
    (F : Submodule ℝ X) [IsClosed (F : Set X)] :
    ¬ Nonempty (TriangularSystem (X ⧸ F) n θ) := by
  rintro ⟨s⟩
  exact hX ⟨s.liftQuotient F⟩

end MarkovSuperreflexivity

end

end OAI
