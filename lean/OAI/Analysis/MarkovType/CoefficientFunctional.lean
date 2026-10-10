import OAI.Analysis.MarkovType.CoefficientBasic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} {K : ℝ} {x : Fin n → E}

theorem CoefficientBasic.norm_term_le (hx : CoefficientBasic K x)
    (a : Fin n → ℝ) (j : Fin n) :
    ‖a j • x j‖ ≤ (2 * K) * ‖∑ i, a i • x i‖ := by
  have hdifference :
      (∑ i : Fin n, if i.val < j.val + 1 then a i • x i else 0) -
        (∑ i : Fin n, if i.val < j.val then a i • x i else 0) = a j • x j := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ i : Fin n, if i = j then a j • x j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i = j
        · subst i
          simp
        · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
          have hiff : i.val < j.val + 1 ↔ i.val < j.val := by omega
          simp only [hiff, ite_eq_right hij, sub_self]
      _ = _ := by simp
  calc
    ‖a j • x j‖ = ‖(∑ i : Fin n, if i.val < j.val + 1 then a i • x i else 0) -
        (∑ i : Fin n, if i.val < j.val then a i • x i else 0)‖ :=
      congrArg norm hdifference.symm
    _ ≤ ‖∑ i : Fin n, if i.val < j.val + 1 then a i • x i else 0‖ +
        ‖∑ i : Fin n, if i.val < j.val then a i • x i else 0‖ := norm_sub_le _ _
    _ ≤ K * ‖∑ i, a i • x i‖ + K * ‖∑ i, a i • x i‖ :=
      add_le_add (hx a (j.val + 1) j.is_lt) (hx a j.val j.is_lt.le)
    _ = _ := by ring

theorem CoefficientBasic.norm_entry_le (hx : CoefficientBasic K x) (j : Fin n) :
    ‖x j‖ ≤ (2 * K) * ‖∑ i, x i‖ := by
  simpa only [one_smul] using hx.norm_term_le (fun _ => 1) j

theorem CoefficientBasic.exists_coordinate_functional (hx : CoefficientBasic K x)
    (hK : 0 ≤ K) (j : Fin n) (hj : x j ≠ 0) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ ≤ 2 * K / ‖x j‖ ∧
      ∀ i : Fin n, f (x i) = if j = i then 1 else 0 := by
  classical
  let T : (Fin n → ℝ) →ₗ[ℝ] E :=
    { toFun := fun a => ∑ i, a i • x i
      map_add' := by
        intro a b
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hjpos : 0 < ‖x j‖ := norm_pos_iff.mpr hj
  have hbound (a : Fin n → ℝ) :
      ‖a j‖ ≤ (2 * K / ‖x j‖) * ‖T a‖ := by
    calc
      ‖a j‖ ≤ (2 * K * ‖T a‖) / ‖x j‖ := by
        apply (le_div_iff₀ hjpos).mpr
        calc
          ‖a j‖ * ‖x j‖ = ‖a j • x j‖ := (norm_smul (a j) (x j)).symm
          _ ≤ 2 * K * ‖T a‖ := hx.norm_term_le a j
      _ = _ := by ring
  have hcoord {a b : Fin n → ℝ} (hab : T a = T b) : a j = b j := by
    have hz : T (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hh := hbound (a - b)
    rw [hz, norm_zero, mul_zero] at hh
    have heq : (a - b) j = 0 := norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
    exact sub_eq_zero.mp heq
  let R : Submodule ℝ E := LinearMap.range T
  let c : R → (Fin n → ℝ) := fun z => Classical.choose z.property
  have hc (z : R) : T (c z) = (z : E) := Classical.choose_spec z.property
  let L : R →ₗ[ℝ] ℝ :=
    { toFun := fun z => c z j
      map_add' := by
        intro z w
        have h := hcoord (a := c (z + w)) (b := c z + c w) (by
          rw [hc, map_add, hc, hc]
          rfl)
        exact h
      map_smul' := by
        intro a z
        have h := hcoord (a := c (a • z)) (b := a • c z) (by
          rw [hc, map_smul, hc]
          rfl)
        exact h }
  have hL (z : R) : ‖L z‖ ≤ (2 * K / ‖x j‖) * ‖z‖ := by
    have h := hbound (c z)
    rw [hc] at h
    exact h
  let F : R →L[ℝ] ℝ := L.mkContinuous (2 * K / ‖x j‖) hL
  have hF : ‖F‖ ≤ 2 * K / ‖x j‖ :=
    L.mkContinuous_norm_le (div_nonneg (mul_nonneg (by norm_num) hK) hjpos.le) hL
  obtain ⟨f, hf, hnorm⟩ := exists_extension_norm_eq R F
  refine ⟨f, hnorm.trans_le hF, ?_⟩
  intro i
  have hTi : T (Pi.single i 1) = x i := by simp [T, Pi.single_apply]
  let z : R := ⟨x i, ⟨Pi.single i 1, hTi⟩⟩
  have hcz : c z j = (Pi.single i (1 : ℝ) : Fin n → ℝ) j := hcoord ((hc z).trans hTi.symm)
  calc
    f (x i) = F z := hf z
    _ = c z j := rfl
    _ = (Pi.single i (1 : ℝ) : Fin n → ℝ) j := hcz
    _ = if j = i then 1 else 0 := by simp [Pi.single_apply]

end MarkovSuperreflexivity

end

end OAI
