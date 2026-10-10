import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveSmallArrayFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem exists_near_adaptiveSmallArrayFamily {L Z M : ℕ} (hL : Squarefree L)
    (hZ : 1 ≤ Z) (hLZ : L ≤ Z) (hC : adaptiveArrayConstant ≤ (Z:ℝ)) (hM : Odd M)
    {lam : ℝ} (hlam : |lam| ≤ 1) (A : ∀ p : ℕ, Finset (ZMod p)) (h : ℤ)
    {θ R : ℝ} (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1)
    (hRlo : (L^6:ℕ) ≤ R) (hRhi : R ≤ (2*Z^13:ℕ)) :
    ∃ a ∈ adaptiveSmallBaseParameters L Z,
      adaptiveSmallArray L lam A a ∈ adaptiveSmallArrayFamily L Z lam A ∧
      ∀ s : ℕ,‖adaptiveActualSmallArray L M lam A R h θ s-adaptiveSmallArray L lam A a s‖ ≤
        (Z:ℝ)^(-(80:ℝ)) := by
  classical
  obtain ⟨a,ha,hMa,hha,hta,hRa⟩ := exists_near_adaptiveSmallBaseParameters hL.ne_zero.bot_lt (by omega)
    (Nat.mod_lt M (by have := hL.ne_zero.bot_lt; omega)) (adaptivePhaseResidue_lt hL.ne_zero.bot_lt h)
    ht0 ht1 hRlo hRhi
  have hab := mem_adaptiveArrayParameters (Finset.mem_filter.mp ha).1 (by omega)
  refine ⟨a,ha,Finset.mem_image.mpr ⟨a,ha,rfl⟩,?_⟩
  intro s
  by_cases hs : s ∈ adaptiveSmallSupport L
  · simp only [adaptiveActualSmallArray,adaptiveSmallArray,ite_eq_left hs]
    rw [positiveDivisorArray_canonical_reduction hL hM,hMa,hha]
    have hsI := Finset.mem_Icc.mp (Finset.mem_filter.mp (adaptiveSmallSupport_subset hZ hLZ hs)).1
    have hRone : (1:ℝ) ≤ R := (show (1:ℝ) ≤ (L^6:ℕ) from by exact_mod_cast Nat.one_le_pow 6 L hL.ne_zero.bot_lt).trans hRlo
    exact (positiveDivisorArray_grid_error hL hZ hLZ hsI.1 hsI.2 (M%(4*L)) 1 hlam A
      (adaptiveInverse (M%(4*L))) hRone hab.2.2.2.2.2.2.1 hRhi hab.2.2.2.2.2.2.2
      (adaptivePhaseResidue L h) hta hRa).trans (adaptiveArray_error_le hZ hC)
  · simp only [adaptiveActualSmallArray,adaptiveSmallArray,ite_eq_right hs,sub_self,norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem adaptive_small_radius_lower {L Z : ℕ} (hZ : 1 ≤ Z) (hLZ : L ≤ Z)
    {R : ℝ} (hR : (Z^10:ℕ) ≤ R) : (L^6:ℕ) ≤ R := by
  have hh : L^6 ≤ Z^10 := (Nat.pow_le_pow_left hLZ 6).trans
    (Nat.pow_le_pow_right hZ (by omega))
  exact (by exact_mod_cast hh : ((L^6:ℕ):ℝ) ≤ (Z^10:ℕ)).trans hR

theorem eventually_near_adaptiveOffEventArrayFamily :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T → 1 ≤ z →
      T^auxiliaryExponent/2 ≤ Real.log z → Real.log z ≤ 2*T^auxiliaryExponent →
      ∀ L M : ℕ, Squarefree L → 1 ≤ Z → L ≤ Z → adaptiveArrayConstant ≤ (Z:ℝ) → Odd M →
      ∀ lam : ℝ, |lam| ≤ 1 → ∀ A : ∀ p : ℕ, Finset (ZMod p), ∀ h : ℤ, ∀ θ R : ℝ,
      0 ≤ θ → θ ≤ 1 → (Z^10:ℕ) ≤ R → R ≤ (2*Z^13:ℕ) →
      adaptiveNoSmallWitness L M A R h θ (auxiliaryK Z z) →
      ∃ a ∈ adaptiveOffEventParameters L Z A (auxiliaryK Z z),
        adaptiveSmallArray L lam A a ∈ adaptiveOffEventArrayFamily L Z lam A (auxiliaryK Z z) ∧
        ∀ s : ℕ,‖adaptiveActualSmallArray L M lam A R h θ s-adaptiveSmallArray L lam A a s‖ ≤
          (Z:ℝ)^(-(80:ℝ)) := by
  filter_upwards [eventually_auxiliary_small_grid_absorption] with T hT
  intro Z z hZl hZu hz hzl hzu L M hL hZ hLZ hC hM lam hlam A h θ R ht0 ht1 hRlo hRhi hno
  obtain ⟨hK,hKlog⟩ := hT Z z hZl hZu hz hzl hzu
  exact exists_near_adaptiveOffEventArrayFamily hL hZ hLZ hC hM hlam A h ht0 ht1
    (adaptive_small_radius_lower hZ hLZ hRlo) hRhi hK hKlog hno

theorem adaptiveSmallArray_total_error {L Z : ℕ} (hZ : 1 ≤ Z) (hLZ : L ≤ Z)
    (a b : ℕ → ℂ) (hnear : ∀ s,‖a s-b s‖ ≤ (Z:ℝ)^(-(80:ℝ))) :
    ∑ s ∈ adaptiveSmallSupport L,‖a s-b s‖ ≤ (Z:ℝ)^(-(66:ℝ)) := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg (adaptiveSmallSupport_subset hZ hLZ)
    (fun s _ _ => norm_nonneg (a s-b s))).trans
    (adaptiveArray_total_error hZ a b (fun s _ => hnear s))

end Ostmann.QuadraticCenter

end

end OAI
