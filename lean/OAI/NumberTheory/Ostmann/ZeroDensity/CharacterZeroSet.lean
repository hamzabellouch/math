import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterFullZeroCount

namespace OAI

/-! # Finiteness and multiplicity of actual zeros in bounded strips -/

namespace Ostmann

open Metric Set MeromorphicOn
open scoped BigOperators Classical

theorem characterZeroOrder_eq_nat (χ : PrimitiveComplexCharacter) (z : ℂ) :
    characterZeroOrder χ z = (analyticOrderNatAt χ.L z : ℤ) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (χ.L_order_ne_top z)
  rw [characterZeroOrder, AnalyticOnNhd.divisor_apply
    (show AnalyticOnNhd ℂ χ.L univ from fun z _ => χ.L_analytic z) (mem_univ z)]
  simp [analyticOrderNatAt, ← hn]

theorem characterZeroOrder_pos_iff (χ : PrimitiveComplexCharacter) (z : ℂ) :
    0 < characterZeroOrder χ z ↔ χ.L z = 0 := by
  rw [characterZeroOrder_eq_nat, Int.natCast_pos]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (χ.L_order_ne_top z)
  have hnat : analyticOrderNatAt χ.L z = n := by simp [analyticOrderNatAt, ← hn]
  rw [hnat]
  have hf := (χ.L_analytic z).analyticOrderAt_ne_zero
  have hnzero : n ≠ 0 ↔ χ.L z = 0 := by simpa only [← hn, Nat.cast_ne_zero] using hf
  exact Nat.pos_iff_ne_zero.trans hnzero

def complexCharacterZeros (χ : PrimitiveComplexCharacter) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < 1 ∧ χ.L z = 0}

theorem PrimitiveComplexCharacter.strip_zeros_finite (χ : PrimitiveComplexCharacter) (T : ℝ) :
    {z : ℂ | z ∈ complexCharacterZeros χ ∧ |z.im| ≤ T}.Finite := by
  by_cases hT : 0 ≤ T
  · let K := closedBall (0 : ℂ) (T + 1)
    have ha : AnalyticOnNhd ℂ χ.L K := fun z _ => χ.L_analytic z
    apply ((divisor χ.L K).finiteSupport (isCompact_closedBall _ _)).subset
    intro z hz
    obtain ⟨⟨hr, hr', hzero⟩, hi⟩ := hz
    have hzK : z ∈ K := by
      rw [mem_closedBall, dist_zero_right]
      have hn := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos hr] at hn
      linarith
    have hdiv : divisor χ.L K z = characterZeroOrder χ z := by
      rw [ha.divisor_apply hzK, characterZeroOrder,
        AnalyticOnNhd.divisor_apply
          (show AnalyticOnNhd ℂ χ.L univ from fun z _ => χ.L_analytic z) (mem_univ z)]
    change divisor χ.L K z ≠ 0
    rw [hdiv]
    exact ne_of_gt ((characterZeroOrder_pos_iff χ z).mpr hzero)
  · have he : {z : ℂ | z ∈ complexCharacterZeros χ ∧ |z.im| ≤ T} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hT ((abs_nonneg z.im).trans hz.2)
    rw [he]
    exact finite_empty

theorem PrimitiveComplexCharacter.zeros_countable (χ : PrimitiveComplexCharacter) :
    (complexCharacterZeros χ).Countable := by
  apply (Set.countable_iUnion (fun n : ℕ => (χ.strip_zeros_finite (n : ℝ)).countable)).mono
  intro z hz
  obtain ⟨n, hn⟩ := exists_nat_ge |z.im|
  exact Set.mem_iUnion.mpr ⟨n, hz, hn⟩

end Ostmann

end OAI
