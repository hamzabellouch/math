import OAI.NumberTheory.TotientAsymptotic.SurvivingBands
import OAI.NumberTheory.TotientAsymptotic.ResidualAlignment

namespace OAI

/-! Normality aligns the actual surviving shifted-prime lists. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- The canceled witness identity, separated bands and small residual primes
supply every hypothesis of the factor-count alignment argument. -/
theorem surviving_largest_factor_alignment : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, 1 ≤ i → i ≤ R x H → L x H < m x → R x H < L x H → p.Prime →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
    tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ) →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i →
    (∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ → ∀ y : ℝ,
    1 < normalityScale x i → 0 ≤ B (normalityScale x i) → normalityScale x i ≤ y →
    0 < B y → B y ≤ 2*fordBandScale x i →
    (∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 : ℕ) ≤ y ∧
      ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 : ℕ) ≤ y) →
    ∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      |B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1))-
        B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1))| ≤
        (2*(r.val : ℝ)+1)*Real.sqrt (B (normalityScale x i)*B y) := by
  filter_upwards [surviving_largest_factor_bands,collision_normality_below_cutoff,
    collision_residual_below_cutoff,eventually_collision_indices] with H hband hnormal hres hind
  filter_upwards [hband,hnormal,hres,m_tendsto.eventually (eventually_ge_atTop H)]
    with x hbands hnormcut hrescut hm
  intro i p q hi hiR hL hR hp η ξ hη hξ hv hfirst hcommon hgη hgξ y hS hBS hSy hBy hByu hsize
  have hk := (hind x hm i hiR).2.2
  have hik : i ≤ collisionLastIndex x i := Nat.le_add_right _ _
  have hg := surviving_good_conditions hiR hgη hgξ
  have hb := hbands i p q hi hiR hL η ξ hη hξ hgη hgξ y hS hBS hSy hBy hByu hsize
  have hD : (suffixPreimage η (collisionLastIndex x i)).totient ≠ 0 :=
    (Nat.totient_pos.mpr (suffixPreimage_pos hη)).ne'
  have hD' : (suffixPreimage ξ (collisionLastIndex x i)).totient ≠ 0 :=
    (Nat.totient_pos.mpr (suffixPreimage_pos hξ)).ne'
  apply ordered_largest_factor_alignment_smooth_cutoff
    (survivingPair p q η ξ i (collisionLastIndex x i)).left
    (survivingPair p q η ξ i (collisionLastIndex x i)).right hS
    (hnormcut i hiR).le hD hD'
    (fun r => (hg r).1) (fun r => (hg r).2.1)
    (surviving_collision_identity hη hξ hp hL hR hk hik hv hfirst hcommon)
    (hrescut i hiR η hη).le (hrescut i hiR ξ hξ).le
    (fun r => (hb.1 r).le) (fun r s hrs => (hb.2 r s hrs).le)
  intro r
  have hleft : (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1) : ℝ) ≤ y := by
    have hp1 : 1 ≤ (survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 := by
      have := (hg r).1.1.two_le
      omega
    exact (show (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1) : ℝ) ≤
      ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 : ℕ) by
      exact_mod_cast largestPrimeFactor_le_self hp1).trans (hsize r).1
  have hright : (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1) : ℝ) ≤ y := by
    have hp1 : 1 ≤ (survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 := by
      have := (hg r).2.1.1.two_le
      omega
    exact (show (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1) : ℝ) ≤
      ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 : ℕ) by
      exact_mod_cast largestPrimeFactor_le_self hp1).trans (hsize r).2
  have hmax1 : (1 : ℝ) < max
      (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1) : ℝ)
      (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1) : ℝ) := by
    have hZ : 1 < collisionSmoothCutoff x i := Real.one_lt_exp_iff.mpr (Real.exp_pos _)
    exact (hZ.trans (hb.1 r)).trans_le ((min_le_left _ _).trans (le_max_left _ _))
  have hBm := Real.log_le_log (Real.log_pos hmax1)
    (Real.log_le_log (zero_lt_one.trans hmax1) (max_le hleft hright))
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hBm hBS)

lemma normalized_alignment_bound {u v B e : ℝ} {j : ℕ} (hB : 0 < B)
    (h : |u-v| ≤ (2*(j : ℝ)+1)*e) :
    |u/B-v/B| ≤ (2*(j : ℝ)+1)*(e/B) := by
  rw [← sub_div,abs_div,abs_of_pos hB]
  exact (div_le_div_of_nonneg_right h hB.le).trans_eq (by ring)

end TotientAsymptotic

end

end OAI
