import OAI.Analysis.MarkovType.FailureJApproximation
import OAI.Analysis.MarkovType.FiniteTailCorrection
import OAI.Analysis.MarkovType.TriangularBasic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section
open scoped BigOperators

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def finiteArrayRealize {n : ℕ} (x : Fin n → X) : (Fin n → ℝ) →ₗ[ℝ] X where
  toFun a := ∑ i, a i • x i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

@[simp] theorem finiteArrayRealize_apply {n : ℕ} (x : Fin n → X) (a : Fin n → ℝ) :
    finiteArrayRealize x a = ∑ i, a i • x i := rfl

@[simp] theorem finiteArrayRealize_single {n : ℕ} (x : Fin n → X) (i : Fin n) :
    finiteArrayRealize x (Pi.single i 1) = x i := by
  classical
  simp [finiteArrayRealize, Pi.single_apply]

namespace ApproximateTailSystem

variable {n : ℕ} {η : ℝ}

theorem realization_pairing_error (s : ApproximateTailSystem X n η)
    (a : Fin n → ℝ) (j : Fin n) :
    |s.functionals j (finiteArrayRealize s.vectors a) - finiteCoefficientTail a j| ≤
      η * ∑ i, |a i| := by
  classical
  have heq : s.functionals j (finiteArrayRealize s.vectors a) - finiteCoefficientTail a j =
      ∑ i, a i * (s.functionals j (s.vectors i) - if j ≤ i then 1 else 0) := by
    simp only [finiteArrayRealize_apply, map_sum, map_smul, smul_eq_mul, finiteCoefficientTail]
    simp_rw [mul_sub, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_sub_distrib]
  rw [heq]
  calc
    |∑ i, a i * (s.functionals j (s.vectors i) - if j ≤ i then 1 else 0)|
        ≤ ∑ i, |a i * (s.functionals j (s.vectors i) - if j ≤ i then 1 else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * η := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (s.pairing_error i j) (abs_nonneg _)
    _ = η * ∑ i, |a i| := by rw [← Finset.sum_mul]; ring

theorem finiteTail_le_realization_add_error (s : ApproximateTailSystem X n η)
    (a : Fin n → ℝ) (j : Fin n) :
    |finiteCoefficientTail a j| ≤ ‖finiteArrayRealize s.vectors a‖ + η * ∑ i, |a i| := by
  have hf : |s.functionals j (finiteArrayRealize s.vectors a)| ≤
      ‖finiteArrayRealize s.vectors a‖ := by
    rw [← Real.norm_eq_abs]
    exact ((s.functionals j).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (s.functionals_bound j) (norm_nonneg _)).trans_eq
        (one_mul _))
  have ht : |finiteCoefficientTail a j| ≤
      |s.functionals j (finiteArrayRealize s.vectors a)| +
        |s.functionals j (finiteArrayRealize s.vectors a) - finiteCoefficientTail a j| := by
    calc
      |finiteCoefficientTail a j| =
          |s.functionals j (finiteArrayRealize s.vectors a) -
            (s.functionals j (finiteArrayRealize s.vectors a) - finiteCoefficientTail a j)| := by
        congr 1
        ring
      _ ≤ _ := abs_sub _ _
  exact ht.trans (add_le_add hf (s.realization_pairing_error a j))

def exactHalf (s : ApproximateTailSystem X n η) (hη : 0 ≤ η)
    (hsmall : 2 * (n : ℝ) * η ≤ 1 / 2) : TriangularSystem X n (1 / 2) := by
  classical
  let A : (Fin n → ℝ) →ₗ[ℝ] X := finiteArrayRealize s.vectors
  have htail (a : Fin n → ℝ) (j : Fin n) : |finiteCoefficientTail a j| ≤ 2 * ‖A a‖ :=
    finiteTail_le_two_norm_of_approx A hη hsmall
      (fun a j => s.finiteTail_le_realization_add_error a j) a j
  have hz (a : Fin n → ℝ) (ha : A a = 0) : a = 0 := by
    apply eq_zero_of_finiteTail_eq_zero
    intro j
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    simpa only [ha, norm_zero, mul_zero] using htail a j
  have hA : Function.Injective A := by
    intro a b hab
    have hab0 : A (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hz (a - b) hab0)
  let E : Submodule ℝ X := LinearMap.range A
  let e : (Fin n → ℝ) ≃ₗ[ℝ] E := LinearEquiv.ofInjective A hA
  have hAinv (z : E) : A (e.symm z) = (z : X) :=
    LinearEquiv.ofInjective_symm_apply A z
  let tailOnImage (j : Fin n) : E →ₗ[ℝ] ℝ :=
    (1 / 2 : ℝ) • ((finiteTailLinear n j).comp e.symm.toLinearMap)
  have htailOnImage (j : Fin n) (z : E) : ‖tailOnImage j z‖ ≤ 1 * ‖z‖ := by
    change ‖(1 / 2 : ℝ) * finiteCoefficientTail (e.symm z) j‖ ≤ 1 * ‖z‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have ht := htail (e.symm z) j
    rw [hAinv] at ht
    change |finiteCoefficientTail (e.symm z) j| ≤ 2 * ‖z‖ at ht
    nlinarith
  let f (j : Fin n) : StrongDual ℝ E :=
    (tailOnImage j).mkContinuous 1 (htailOnImage j)
  have hfnorm (j : Fin n) : ‖f j‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    exact htailOnImage j
  have hext (j : Fin n) : ∃ F : StrongDual ℝ X,
      (∀ z : E, F (z : X) = f j z) ∧ ‖F‖ ≤ 1 := by
    obtain ⟨F, hF, hFnorm⟩ := exists_extension_norm_eq E (f j)
    exact ⟨F, hF, hFnorm.trans_le (hfnorm j)⟩
  let F (j : Fin n) : StrongDual ℝ X := Classical.choose (hext j)
  have hF (j : Fin n) : ∀ z : E, F j (z : X) = f j z :=
    (Classical.choose_spec (hext j)).1
  have hFnorm (j : Fin n) : ‖F j‖ ≤ 1 := (Classical.choose_spec (hext j)).2
  refine {
    vectors := s.vectors
    functionals := F
    vectors_bound := s.vectors_bound
    functionals_bound := hFnorm
    pairing := ?_ }
  intro i j
  have hf := hF j (e (Pi.single i 1))
  change F j (A (Pi.single i 1)) =
    (1 / 2 : ℝ) * finiteCoefficientTail (e.symm (e (Pi.single i 1))) j at hf
  rw [e.symm_apply_apply] at hf
  simpa only [A, finiteArrayRealize_single, finiteTail_single,
    mul_ite, mul_one, mul_zero] using hf

end ApproximateTailSystem

theorem exact_triangular_system_of_not_jConvex (h : ¬ AmbientJConvex X) (n : ℕ) :
    Nonempty (TriangularSystem X n (1 / 2)) := by
  let N := n + 2
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let η : ℝ := 1 / (4 * (N : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨s⟩ := approximateTailSystem_of_not_jConvex h N hN η hη
  have hsmall : 2 * (N : ℝ) * η ≤ 1 / 2 := by
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have heq : 2 * (N : ℝ) * η = (1 / 2 : ℝ) := by
      dsimp [η]
      field_simp [hNne]
      ; ring
    exact heq.le
  exact ⟨(s.exactHalf hη.le hsmall).restrict (by dsimp [N]; omega)⟩

theorem not_finiteTriangularObstruction_of_not_jConvex (h : ¬ AmbientJConvex X) :
    ¬ FiniteTriangularObstruction X := by
  intro hobs
  obtain ⟨n, _, hn⟩ := hobs (1 / 2) (by norm_num) (by norm_num)
  exact hn (exact_triangular_system_of_not_jConvex h n)

theorem FiniteTriangularObstruction.ambientJConvex
    (h : FiniteTriangularObstruction X) : AmbientJConvex X := by
  by_contra hn
  exact not_finiteTriangularObstruction_of_not_jConvex hn h

end MarkovSuperreflexivity

end

end OAI
