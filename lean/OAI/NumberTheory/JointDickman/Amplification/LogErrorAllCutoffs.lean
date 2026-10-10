import OAI.NumberTheory.JointDickman.Analysis.SquarefreeDirichletSeries
import Mathlib.Analysis.Asymptotics.Defs

namespace OAI

/-! # Extending an asymptotic error to every cutoff at least three -/
namespace JointDickman
open Filter Asymptotics Set Finset
open scoped Topology

theorem squarefreeSummatory_abs_le {z x : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hx : 0 ≤ x) :
    |squarefreeSummatory z x| ≤ x := by
  unfold squarefreeSummatory
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, |squarefreeWeight z n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Ioc 0 ⌊x⌋₊, (1:ℝ) := sum_le_sum (fun n _ => squarefreeWeight_abs_le_one hz hz1 n)
    _ = (⌊x⌋₊:ℝ) := by simp
    _ ≤ x := Nat.floor_le hx

theorem log_error_all_cutoffs {A P : ℝ → ℝ} {μ : ℝ}
    (hA : ∀ x : ℝ, 3 ≤ x → |A x| ≤ x)
    (hP : ∀ x : ℝ, 3 ≤ x → ContinuousAt P x)
    (he : (fun x : ℝ => A x-x*P x) =O[atTop] (fun x => x*(Real.log x)^μ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x →
      |A x-x*P x| ≤ C*x*(Real.log x)^μ := by
  obtain ⟨B,hB,hbound⟩ := isBigO_iff'.mp he
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hbound
  let Y := max 3 x₀
  let G : ℝ → ℝ := fun x => (1+|P x|)/(Real.log x)^μ
  have hG : ContinuousOn G (Icc 3 Y) := by
    intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    have hl : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
    apply ContinuousAt.continuousWithinAt
    exact (continuousAt_const.add (hP x hx.1).abs).div
      ((Real.continuousAt_log hxpos.ne').rpow_const (Or.inl hl.ne'))
      (Real.rpow_pos_of_pos hl μ).ne'
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  refine ⟨B+|D|+1,by positivity,?_⟩
  intro x hx
  have hxpos : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hp : 0 < (Real.log x)^μ := Real.rpow_pos_of_pos hl μ
  by_cases hxx : x₀ ≤ x
  · have h := hx₀ x hxx
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (mul_pos hxpos hp)] at h
    calc
      _ ≤ B*(x*(Real.log x)^μ) := h
      _ ≤ (B+|D|+1)*(x*(Real.log x)^μ) :=
        mul_le_mul_of_nonneg_right (by linarith [abs_nonneg D]) (mul_pos hxpos hp).le
      _ = _ := by ring
  · have hxY : x ≤ Y := (le_of_not_ge hxx).trans (le_max_right _ _)
    have hg : G x ≤ D := by
      have h := hD x ⟨hx,hxY⟩
      exact (le_abs_self (G x)).trans (by simpa only [Real.norm_eq_abs] using h)
    have hg' : 1+|P x| ≤ D*(Real.log x)^μ := (div_le_iff₀ hp).mp hg
    have ha : |A x-x*P x| ≤ x*(1+|P x|) := by
      calc
        _ ≤ |A x|+|x*P x| := abs_sub _ _
        _ ≤ x+x*|P x| := by rw [abs_mul,abs_of_pos hxpos]; exact add_le_add (hA x hx) le_rfl
        _ = _ := by ring
    calc
      _ ≤ x*(1+|P x|) := ha
      _ ≤ x*(D*(Real.log x)^μ) := mul_le_mul_of_nonneg_left hg' hxpos.le
      _ = D*(x*(Real.log x)^μ) := by ring
      _ ≤ (B+|D|+1)*(x*(Real.log x)^μ) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self D]) (mul_pos hxpos hp).le
      _ = _ := by ring

end JointDickman

end OAI
