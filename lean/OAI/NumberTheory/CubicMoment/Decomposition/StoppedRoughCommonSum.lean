import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonBound
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonEnergy

namespace OAI

/-! Only coefficient-active rows impose roughness.  Common factors below
that threshold vanish before the exact finite sum is estimated. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma active_rough_common_block_zero (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (R : ℝ) (hrough : ∀ a ∈ S, β a ≠ 0 → ∀ p, primaryPrime p → p ∣ a → R ≤ norm p)
    (u : ℝ) (V : ℝ → ℂ) (A : ℝ) {k : Eisenstein}
    (hk : primary k) (hks : Squarefree k) (hk1 : k ≠ 1) (hkR : norm k < R) :
    commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V A k = 0 := by
  unfold commonGramBlock
  apply Finset.sum_eq_zero
  intro a ha
  have hz := rough_small_common_coefficient_zero S β R hrough hk hks hk1 hkR ha
  apply Finset.sum_eq_zero
  intro b hb
  simp only [dispersionAmplitude,hz,zero_mul,star_zero,ite_self]

theorem active_rough_common_blocks_bound (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S I : Finset Eisenstein)
      (β : Eisenstein → ℂ) (Z A M u R : ℝ),
      1 ≤ Z → Z^(3/2:ℝ) ≤ A → 0 ≤ M → 0 < R →
      (∀ k ∈ I, primary k ∧ Squarefree k ∧ k ≠ 1 ∧ 65536 ≤ Z/norm k) →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      (∀ a ∈ S, β a ≠ 0 → ∀ p, primaryPrime p → p ∣ a → R ≤ norm p) →
      ‖∑ k ∈ I, commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V A k‖ ≤
        K*A^(2/3:ℝ)*Z^(5/3:ℝ)*M^2*(1+Real.log Z)^d*R^(-(1/6:ℝ)) := by
  obtain ⟨K,d,hK,hbound⟩ := rough_common_blocks_bound hpnt hHuxley V hV hV'
  refine ⟨K,d,hK,?_⟩
  intro S I β Z A M u R hZ hA hM hR hI hS hβ hrough
  let J := I.filter (fun k => R ≤ norm k)
  have he : (∑ k ∈ I, commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V A k) =
      ∑ k ∈ J, commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V A k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hRk : R ≤ norm k
    · simp only [ite_eq_left hRk]
    · simp only [ite_eq_right hRk]
      exact active_rough_common_block_zero S β R hrough u V A
        (hI k hk).1 (hI k hk).2.1 (hI k hk).2.2.1 (lt_of_not_ge hRk)
  rw [he]
  exact hbound S J β Z A M u R hZ hA hM hR
    (fun k hk => ⟨(hI k (Finset.mem_filter.mp hk).1).1,
      (hI k (Finset.mem_filter.mp hk).1).2.1,(Finset.mem_filter.mp hk).2,
      (hI k (Finset.mem_filter.mp hk).1).2.2.2⟩) hS hβ

end CubicFirstMoment

end

end OAI
