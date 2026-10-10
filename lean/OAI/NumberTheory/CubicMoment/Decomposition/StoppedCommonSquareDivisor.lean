import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRoughCommonSum
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonScale

namespace OAI

/-! The actual common-factor rows still satisfy the bounded-coefficient
estimate after a small square-divisor rescales the outer variable. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem rough_square_divisor_common_blocks (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (j : ℕ), 0 < K ∧ ∀ (S I : Finset Eisenstein)
      (β : Eisenstein → ℂ) (Z A M u R D : ℝ),
      1 ≤ Z → Z^(3/2:ℝ) ≤ A → 0 ≤ M → 0 < R → 1 ≤ D → D^4 ≤ R →
      (∀ k ∈ I, primary k ∧ Squarefree k ∧ k ≠ 1 ∧ 65536 ≤ Z/norm k) →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      (∀ a ∈ S, β a ≠ 0 → ∀ p, primaryPrime p → p ∣ a → R ≤ norm p) →
      ‖∑ k ∈ I, commonGramBlock S (fun a => star (dispersionAmplitude β u a))
        V (A/D^2) k‖ ≤
      K*A^(2/3:ℝ)*Z^(5/3:ℝ)*M^2*(1+Real.log Z)^j*R^(-(1/6:ℝ)) := by
  obtain ⟨K,j,hK,hbound⟩ := rough_common_blocks_at_scale hpnt hHuxley V hV hV'
  refine ⟨K,j,hK,?_⟩
  intro S I β Z A M u R D hZ hA hM hR hD hDR hI hS hβ hrough
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hAp : 0 < A := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _).trans_le hA
  let J := I.filter (fun k => R ≤ norm k)
  have he : (∑ k ∈ I, commonGramBlock S (fun a => star (dispersionAmplitude β u a))
      V (A/D^2) k) = ∑ k ∈ J, commonGramBlock S
        (fun a => star (dispersionAmplitude β u a)) V (A/D^2) k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hRk : R ≤ norm k
    · simp only [ite_eq_left hRk]
    · simp only [ite_eq_right hRk]
      exact active_rough_common_block_zero S β R hrough u V (A/D^2)
        (hI k hk).1 (hI k hk).2.1 (hI k hk).2.2.1 (lt_of_not_ge hRk)
  rw [he]
  have hb := hbound S J β Z (A/D^2) M u R hZ (by positivity) hM hR
    (fun k hk => by
      have hkI := (Finset.mem_filter.mp hk).1
      have hkR := (Finset.mem_filter.mp hk).2
      have hp := (hI k hkI).1
      have hkp := norm_pos_of_ne_zero (primary_ne_zero hp)
      exact ⟨hp,(hI k hkI).2.1,hkR,(hI k hkI).2.2.2,
        square_divisor_common_outer_scale (zero_le_one.trans hZ) hkp hkp le_rfl
          hDp (hDR.trans hkR) hA⟩) hS hβ
  apply hb.trans
  have houter : (A/D^2)^(2/3:ℝ) ≤ A^(2/3:ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (div_le_self hAp.le (one_le_pow₀ hD)) (by norm_num)
  have hlog : 0 ≤ 1+Real.log Z := by linarith [Real.log_nonneg hZ]
  calc
    _ = (K*Z^(5/3:ℝ)*M^2*(1+Real.log Z)^j*R^(-(1/6:ℝ)))*
        (A/D^2)^(2/3:ℝ) := by ring
    _ ≤ (K*Z^(5/3:ℝ)*M^2*(1+Real.log Z)^j*R^(-(1/6:ℝ)))*A^(2/3:ℝ) :=
      mul_le_mul_of_nonneg_left houter (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
