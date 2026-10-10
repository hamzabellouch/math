import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArrayNearest
import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArrayReduction

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem exists_near_adaptiveArrayFamily {L Z M P : ℕ}
    (hL : Squarefree L) (hZ : 1 ≤ Z) (hLZ : L ≤ Z)
    (hC : adaptiveArrayConstant ≤ (Z:ℝ)) (hM : Odd M)
    (hP : 1 ≤ P) (hPZ : P ≤ Z^7) {lam : ℝ} (hlam : |lam| ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) (h : ℤ) {θ R : ℝ}
    (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1) (hR1 : 1 ≤ R) (hRB : R ≤ (2*Z^13:ℕ)) :
    ∃ b ∈ adaptiveArrayFamily L Z lam A, ∀ s ∈ adaptiveArraySupport L Z,
      ‖positiveDivisorArray L M lam A (adaptiveInverse M) P R h θ s-b s‖ ≤
        (Z:ℝ)^(-(80:ℝ)) := by
  obtain ⟨b,hb,hnear⟩ := exists_near_adaptiveArrayFamily_canonical hL hZ hLZ hC
    (Nat.mod_lt M (by have := hL.ne_zero.bot_lt; omega))
    (adaptivePhaseResidue_lt hL.ne_zero.bot_lt h) hP hPZ hlam A ht0 ht1 hR1 hRB
  refine ⟨b,hb,?_⟩
  intro s hs
  have he := hnear s
  simp only [adaptiveContinuousArray,ite_eq_left hs] at he
  rw [positiveDivisorArray_canonical_reduction hL hM]
  exact he

theorem exists_near_adaptiveArrayFamily_of_inverse {L Z M P : ℕ}
    (hL : Squarefree L) (hZ : 1 ≤ Z) (hLZ : L ≤ Z)
    (hC : adaptiveArrayConstant ≤ (Z:ℝ)) (hM : Odd M)
    (hP : 1 ≤ P) (hPZ : P ≤ Z^7) {lam : ℝ} (hlam : |lam| ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    (hmInv : ∀ d ∈ L.divisors, (mInv d:ZMod d)=(M:ZMod d)⁻¹)
    (h : ℤ) {θ R : ℝ} (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1)
    (hR1 : 1 ≤ R) (hRB : R ≤ (2*Z^13:ℕ)) :
    ∃ b ∈ adaptiveArrayFamily L Z lam A, ∀ s ∈ adaptiveArraySupport L Z,
      ‖positiveDivisorArray L M lam A mInv P R h θ s-b s‖ ≤ (Z:ℝ)^(-(80:ℝ)) := by
  obtain ⟨b,hb,hnear⟩ := exists_near_adaptiveArrayFamily hL hZ hLZ hC hM hP hPZ hlam A h ht0 ht1 hR1 hRB
  refine ⟨b,hb,?_⟩
  intro s hs
  have he := hnear s hs
  rw [positiveDivisorArray_canonical_reduction hL hM] at he
  rw [positiveDivisorArray_residue_reduction hL hM lam A mInv hmInv]
  exact he

theorem adaptiveArray_total_error {L Z : ℕ} (hZ : 1 ≤ Z) (a b : ℕ → ℂ)
    (hnear : ∀ s ∈ adaptiveArraySupport L Z, ‖a s-b s‖ ≤ (Z:ℝ)^(-(80:ℝ))) :
    ∑ s ∈ adaptiveArraySupport L Z, ‖a s-b s‖ ≤ (Z:ℝ)^(-(66:ℝ)) := by
  have hz : (0:ℝ)<Z := by exact_mod_cast (show 0<Z by omega)
  have hcard : ((adaptiveArraySupport L Z).card:ℝ) ≤ (Z:ℝ)^14 := by
    exact_mod_cast adaptiveArraySupport_card L Z
  calc
    _ ≤ ∑ _s ∈ adaptiveArraySupport L Z,(Z:ℝ)^(-(80:ℝ)) := Finset.sum_le_sum hnear
    _ = (adaptiveArraySupport L Z).card*(Z:ℝ)^(-(80:ℝ)) := by simp
    _ ≤ (Z:ℝ)^14*(Z:ℝ)^(-(80:ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_add hz]; norm_num

def adaptiveArrayThreshold : ℕ := max 2 ⌈max cutoffFourierBound adaptiveArrayConstant⌉₊

theorem adaptiveArrayFamily_polynomial {L Z : ℕ} (hZ : adaptiveArrayThreshold ≤ Z)
    (hL : Squarefree L) (hLZ : L ≤ Z) {lam : ℝ} (hlam : |lam| ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) :
    (adaptiveArrayFamily L Z lam A).card ≤ Z^430 ∧
      (∀ b ∈ adaptiveArrayFamily L Z lam A,
        ∑ s ∈ adaptiveArraySupport L Z, ‖b s‖ ≤ (Z:ℝ)^430) ∧
      adaptiveArrayConstant ≤ (Z:ℝ) := by
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZ
  have hceil : (⌈max cutoffFourierBound adaptiveArrayConstant⌉₊:ℝ) ≤ Z := by
    exact_mod_cast (le_max_right 2 ⌈max cutoffFourierBound adaptiveArrayConstant⌉₊).trans hZ
  have hmax : max cutoffFourierBound adaptiveArrayConstant ≤ (Z:ℝ) := (Nat.le_ceil _).trans hceil
  exact ⟨adaptiveArrayFamily_card hZ2 hLZ lam A,
    fun b hb => adaptiveArrayFamily_l1 hL (by omega) hLZ ((le_max_left _ _).trans hmax) hlam A hb,
    (le_max_right _ _).trans hmax⟩

end Ostmann.QuadraticCenter

end

end OAI
