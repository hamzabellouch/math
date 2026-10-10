import OAI.Analysis.MarkovType.TriangularBasic
import OAI.Analysis.MarkovType.SeminormUltralimit
import OAI.Analysis.MarkovType.OrderedSequences
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open Filter
open scoped BigOperators

namespace MarkovSuperreflexivity
namespace TriangularLimit

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {θ : ℝ}

def vectorAt (s : ∀ n : ℕ, TriangularSystem X n θ) (n i : ℕ) : X :=
  if hi : i < n then (s n).vectors ⟨i, hi⟩ else 0

theorem vectorAt_bound (s : ∀ n : ℕ, TriangularSystem X n θ) (n i : ℕ) :
    ‖vectorAt s n i‖ ≤ 1 := by
  classical
  by_cases hi : i < n
  · simpa only [vectorAt, dite_eq_left hi] using (s n).vectors_bound ⟨i, hi⟩
  · simp [vectorAt, hi]

def realize (s : ∀ n : ℕ, TriangularSystem X n θ) (n : ℕ) : C00 →ₗ[ℝ] X :=
  Finsupp.linearCombination ℝ (vectorAt s n)

def finiteSeminorm (s : ∀ n : ℕ, TriangularSystem X n θ) (n : ℕ) : Seminorm ℝ C00 :=
  (normSeminorm ℝ X).comp (realize s n)

@[simp] theorem finiteSeminorm_apply (s : ∀ n : ℕ, TriangularSystem X n θ)
    (n : ℕ) (a : C00) : finiteSeminorm s n a = ‖realize s n a‖ := rfl

theorem finiteSeminorm_le (s : ∀ n : ℕ, TriangularSystem X n θ) (n : ℕ) (a : C00) :
    finiteSeminorm s n a ≤ ∑ i ∈ a.support, |a i| := by
  classical
  change ‖∑ i ∈ a.support, a i • vectorAt s n i‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (vectorAt_bound s n i) (abs_nonneg _)).trans_eq
    (mul_one _)

theorem bounded (s : ∀ n : ℕ, TriangularSystem X n θ) (a : C00) :
    RealSeqBounded (fun n => finiteSeminorm s n a) := by
  refine ⟨∑ i ∈ a.support, |a i|, fun n => ?_⟩
  rw [abs_of_nonneg (apply_nonneg (finiteSeminorm s n) a)]
  exact finiteSeminorm_le s n a

def limitNorm (s : ∀ n : ℕ, TriangularSystem X n θ) : Seminorm ℝ C00 :=
  seminormULim freeUltrafilter (finiteSeminorm s) (bounded s)

@[simp] theorem limitNorm_apply (s : ∀ n : ℕ, TriangularSystem X n θ) (a : C00) :
    limitNorm s a = realULim freeUltrafilter (fun n => finiteSeminorm s n a) := rfl

theorem limitNorm_le (s : ∀ n : ℕ, TriangularSystem X n θ) (a : C00) :
    limitNorm s a ≤ ∑ i ∈ a.support, |a i| :=
  realULim_le_of_eventually_le freeUltrafilter (bounded s a)
    (Eventually.of_forall (fun n => finiteSeminorm_le s n a))

def tailForm (θ : ℝ) (j : ℕ) : C00 →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun i => if j ≤ i then θ else 0)

@[simp] theorem tailForm_single (j i : ℕ) (b : ℝ) :
    tailForm θ j (Finsupp.single i b) = b * (if j ≤ i then θ else 0) := by
  simp only [tailForm, Finsupp.linearCombination_single, smul_eq_mul]

theorem finite_pairing (s : ∀ n : ℕ, TriangularSystem X n θ)
    (a : C00) {n j : ℕ} (hj : j < n) (ha : ∀ i ∈ a.support, i < n) :
    (s n).functionals ⟨j, hj⟩ (realize s n a) = tailForm θ j a := by
  classical
  change (s n).functionals ⟨j, hj⟩ (∑ i ∈ a.support, a i • vectorAt s n i) =
    ∑ i ∈ a.support, a i • (if j ≤ i then θ else 0)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  congr 1
  rw [vectorAt, dite_eq_left (ha i hi), (s n).pairing]
  rfl

theorem tailForm_le_finite (s : ∀ n : ℕ, TriangularSystem X n θ)
    (a : C00) {n j : ℕ} (hj : j < n) (ha : ∀ i ∈ a.support, i < n) :
    |tailForm θ j a| ≤ finiteSeminorm s n a := by
  rw [← finite_pairing s a hj ha, ← Real.norm_eq_abs]
  calc
    ‖(s n).functionals ⟨j, hj⟩ (realize s n a)‖ ≤
        ‖(s n).functionals ⟨j, hj⟩‖ * ‖realize s n a‖ :=
      ((s n).functionals ⟨j, hj⟩).le_opNorm _
    _ ≤ 1 * ‖realize s n a‖ :=
      mul_le_mul_of_nonneg_right ((s n).functionals_bound _) (norm_nonneg _)
    _ = finiteSeminorm s n a := one_mul _

theorem tailForm_le (s : ∀ n : ℕ, TriangularSystem X n θ) (a : C00) (j : ℕ) :
    |tailForm θ j a| ≤ limitNorm s a := by
  apply le_realULim_of_eventually_le freeUltrafilter (bounded s a)
  apply freeUltrafilter_le_atTop
  filter_upwards [eventually_ge_atTop (max j (a.support.sup id) + 1)] with n hn
  apply tailForm_le_finite s a (by omega)
  intro i hi
  have his : i ≤ a.support.sup id := Finset.le_sup (f := id) hi
  omega

theorem tailForm_sub (a : C00) (j : ℕ) :
    tailForm θ j a - tailForm θ (j + 1) a = θ * a j := by
  classical
  have h : tailForm θ j - tailForm θ (j + 1) =
      θ • (Finsupp.lapply j : C00 →ₗ[ℝ] ℝ) := by
    apply Finsupp.lhom_ext
    intro i b
    by_cases hij : i = j
    · subst i
      simp [tailForm_single, mul_comm]
    · by_cases hji : j ≤ i
      · have hnext : j + 1 ≤ i := by omega
        simp [tailForm_single, hji, hnext, Ne.symm hij]
      · have hnext : ¬j + 1 ≤ i := by omega
        simp [tailForm_single, hji, hnext, Ne.symm hij]
  exact congrArg (fun T : C00 →ₗ[ℝ] ℝ => T a) h

theorem coordinate_bound (s : ∀ n : ℕ, TriangularSystem X n θ)
    (a : C00) (j : ℕ) : |θ * a j| ≤ 2 * limitNorm s a := by
  rw [← tailForm_sub a j]
  calc
    |tailForm θ j a - tailForm θ (j + 1) a| ≤
        |tailForm θ j a| + |tailForm θ (j + 1) a| := abs_sub _ _
    _ ≤ limitNorm s a + limitNorm s a := add_le_add (tailForm_le s a j)
      (tailForm_le s a (j + 1))
    _ = 2 * limitNorm s a := by ring

theorem definite (s : ∀ n : ℕ, TriangularSystem X n θ) (hθ : 0 < θ) :
    ∀ a : C00, limitNorm s a = 0 → a = 0 := by
  intro a ha
  ext j
  have hz : |θ * a j| = 0 := le_antisymm (by simpa [ha] using coordinate_bound s a j)
    (abs_nonneg _)
  have hp : θ * a j = 0 := abs_eq_zero.mp hz
  exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt hθ)

theorem basis_bound (s : ∀ n : ℕ, TriangularSystem X n θ) (i : ℕ) :
    limitNorm s (C00.basis i) ≤ 1 := by
  apply realULim_le_of_eventually_le freeUltrafilter (bounded s (C00.basis i))
  apply Eventually.of_forall
  intro n
  simpa only [finiteSeminorm_apply, realize, C00.basis,
    Finsupp.linearCombination_single, one_smul] using vectorAt_bound s n i

@[simp] theorem tailForm_basis (j i : ℕ) :
    tailForm θ j (C00.basis i) = if j ≤ i then θ else 0 := by
  simp only [C00.basis, tailForm_single, one_mul]

end TriangularLimit
end MarkovSuperreflexivity

end

end OAI
