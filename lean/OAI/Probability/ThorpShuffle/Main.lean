import OAI.Probability.ThorpShuffle.EightBlocks

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

theorem full_mixing :
    Tendsto (fun d : ℕ => distance d (1600 * d)) atTop (nhds 0) := by
  apply (tendsto_add_atTop_iff_nat 3).mp
  simpa only [Nat.add_assoc] using Block.full_mixing_shift

theorem mixingTime_isBigO_orderFunction :
    Asymptotics.IsBigO atTop (fun d : ℕ => (mixingTime d : ℝ)) orderFunction := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1600, ?_⟩
  have he : ∀ᶠ d : ℕ in atTop, distance d (1600*d) < 1/4 :=
    full_mixing.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/4))
  filter_upwards [he] with d hd
  have ht : mixingTime d ≤ 1600*d := Nat.sInf_le hd.le
  simp only [orderFunction, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (mixingTime d)),
    abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d)]
  exact_mod_cast ht

theorem mixingTime_isTheta_orderFunction :
    Asymptotics.IsTheta atTop (fun d : ℕ => (mixingTime d : ℝ)) orderFunction :=
  ⟨mixingTime_isBigO_orderFunction, orderFunction_isBigO_mixingTime⟩

theorem mixingTime_isTheta_log :
    Asymptotics.IsTheta atTop (fun d : ℕ => (mixingTime d : ℝ))
      (fun d : ℕ => Real.log (2^d : ℝ)) := by
  have h := Asymptotics.IsTheta.const_mul_right
    (show Real.log 2 ≠ 0 from (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne')
    mixingTime_isTheta_orderFunction
  simpa only [orderFunction, Real.log_pow, mul_comm] using h

theorem main :
    Tendsto (fun d : ℕ => distance d (1600 * d)) atTop (nhds 0) ∧
    (∀ d : ℕ, 1 ≤ d → ∃ t : ℕ, distance d t ≤ 1 / 4) ∧
    (∀ (d t : ℕ) (g₀ : State d), tv (lawFrom d t g₀) (uniform d) = distance d t) ∧
    (∀ d : ℕ, 1 ≤ d → supportThreshold d ≤ (mixingTime d : ℤ)) ∧
    Asymptotics.IsBigO atTop
      (fun d : ℕ => (supportThreshold d : ℝ) - 2 * (d : ℝ)) (fun _ => (1 : ℝ)) ∧
    Asymptotics.IsTheta atTop (fun d : ℕ => (mixingTime d : ℝ)) orderFunction ∧
    Asymptotics.IsTheta atTop (fun d : ℕ => (mixingTime d : ℝ))
      (fun d : ℕ => Real.log (2 ^ d : ℝ)) := by
  exact ⟨full_mixing, fun _ hd => exists_mixing_time hd, worst_start_eq,
    fun _ hd => exact_support_lower hd, supportThreshold_isBigO,
    mixingTime_isTheta_orderFunction, mixingTime_isTheta_log⟩

end Thorp

end

end OAI
