import OAI.Analysis.Cotype.Target

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [AddCommMonoid E] [Module ℝ E]

theorem average_sum (f : κ → ι → E) :
    average (fun i => ∑ k, f k i) = ∑ k, average (f k) := by
  simp only [average, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem average_smul_const (a : ι → ℝ) (x : E) :
    average (fun i => a i • x) = average a • x := by
  simp only [average, smul_eq_mul]
  rw [← Finset.sum_smul, smul_smul]

def unitIndex {n : ℕ} (i : Fin n) : Cube n := fun j => decide (i = j)

@[simp] theorem character_unitIndex {n : ℕ} (i : Fin n) (ε : Cube n) :
    character (unitIndex i) ε = sign (ε i) := by
  simp [character, unitIndex]

theorem unitIndex_injective {n : ℕ} : Function.Injective (@unitIndex n) := by
  intro i j h
  have hh := congrFun h i
  simpa [unitIndex, eq_comm] using hh.symm

theorem coordinate_orthogonality {n : ℕ} (i j : Fin n) :
    average (fun ε : Cube n => sign (ε i) * sign (ε j)) = if i = j then 1 else 0 := by
  simpa [unitIndex_injective.eq_iff] using average_character_mul (unitIndex i) (unitIndex j)

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem moment_rademacherSum {n : ℕ} (x : Fin n → X) (i : Fin n) :
    moment X (rademacherSum X x) i = x i := by
  simp only [moment, rademacherSum, Finset.smul_sum, smul_smul]
  rw [average_sum]
  simp_rw [average_smul_const, coordinate_orthogonality]
  simp

theorem moment_surjective (n : ℕ) :
    Function.Surjective (@moment X _ _ n) := by
  intro x
  exact ⟨rademacherSum X x, funext (moment_rademacherSum X x)⟩

theorem radProjection_rademacherSum {n : ℕ} (x : Fin n → X) :
    radProjection X (rademacherSum X x) = rademacherSum X x := by
  unfold radProjection
  congr 1
  funext i
  exact moment_rademacherSum X x i

theorem radProjection_idempotent {n : ℕ} (f : Cube n → X) :
    radProjection X (radProjection X f) = radProjection X f :=
  radProjection_rademacherSum X (moment X f)

end Cotype

end

end OAI
