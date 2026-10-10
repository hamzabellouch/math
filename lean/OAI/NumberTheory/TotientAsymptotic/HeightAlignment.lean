import OAI.NumberTheory.TotientAsymptotic.ActualSurvivingGeometry
import OAI.NumberTheory.TotientAsymptotic.ResidualAlignment
import OAI.NumberTheory.TotientAsymptotic.SurvivingBands

namespace OAI

/-! Alignment of prime heights, including the largest prime. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma height_bounds_factor_order {b : ℕ} {t : ShiftedPair b} {Y Z : ℝ}
    (hZ : 0<Z) (ht : ComparisonHeightBounds t Y Z) :
    (∀ r, Real.exp (Real.exp ((7/10 : ℝ)*Z)) <
      min (largestPrimeFactor (t.left r-1) : ℝ) (largestPrimeFactor (t.right r-1) : ℝ)) ∧
    (∀ r s, r<s → max (largestPrimeFactor (t.left s-1) : ℝ) (largestPrimeFactor (t.right s-1) : ℝ) <
      min (largestPrimeFactor (t.left r-1) : ℝ) (largestPrimeFactor (t.right r-1) : ℝ)) := by
  have hposL (r : Fin b) : (1 : ℝ)<largestPrimeFactor (t.left r-1) := by
    exact_mod_cast one_lt_nat_of_doubleLog_pos (ht.positive r).1
  have hposR (r : Fin b) : (1 : ℝ)<largestPrimeFactor (t.right r-1) := by
    exact_mod_cast one_lt_nat_of_doubleLog_pos (ht.positive r).2
  constructor
  · intro r
    have hc := ht.bottom r
    have hlow : (7/10 : ℝ)*Z < min (leftFactorHeight t r) (rightFactorHeight t r) := by linarith
    have he : B (Real.exp (Real.exp ((7/10 : ℝ)*Z)))=(7/10 : ℝ)*Z := by
      simp only [B,Real.log_exp]
    have h1 : 1<Real.exp (Real.exp ((7/10 : ℝ)*Z)) := Real.one_lt_exp_iff.mpr (Real.exp_pos _)
    exact lt_min (lt_of_doubleLog_lt h1 (hposL r) (by rw [he]; exact hlow.trans_le (min_le_left _ _)))
      (lt_of_doubleLog_lt h1 (hposR r) (by rw [he]; exact hlow.trans_le (min_le_right _ _)))
  · intro r s hrs
    have hc := ht.separated r s hrs
    have hh : max (leftFactorHeight t s) (rightFactorHeight t s) <
        min (leftFactorHeight t r) (rightFactorHeight t r) := by linarith
    have hlL : leftFactorHeight t s < leftFactorHeight t r :=
      (le_max_left _ _).trans_lt (hh.trans_le (min_le_left _ _))
    have hlR : leftFactorHeight t s < rightFactorHeight t r :=
      (le_max_left _ _).trans_lt (hh.trans_le (min_le_right _ _))
    have hrL : rightFactorHeight t s < leftFactorHeight t r :=
      (le_max_right _ _).trans_lt (hh.trans_le (min_le_left _ _))
    have hrR : rightFactorHeight t s < rightFactorHeight t r :=
      (le_max_right _ _).trans_lt (hh.trans_le (min_le_right _ _))
    exact max_lt (lt_min (lt_of_doubleLog_lt (hposL s) (hposL r) hlL)
      (lt_of_doubleLog_lt (hposL s) (hposR r) hlR))
      (lt_min (lt_of_doubleLog_lt (hposR s) (hposL r) hrL)
        (lt_of_doubleLog_lt (hposR s) (hposR r) hrR))

lemma alignment_of_height_bounds {b D : ℕ} {t : ShiftedPair b} {y S Z : ℝ}
    (hS : 1<S) (hBS : 0≤B S) (hSZ : S≤Real.exp (Real.exp ((7/10 : ℝ)*Z)))
    (hZ : 0<Z) (ht : ComparisonHeightBounds t (B y) Z)
    (hD : D≠0) (hD' : t.remainder≠0)
    (hnorm : ∀ r, IsNormalPrime S (t.left r) ∧ IsNormalPrime S (t.right r))
    (heq : D*shiftedProduct t.left=t.remainder*shiftedProduct t.right)
    (hsmooth : (largestPrimeFactor D : ℝ)≤Real.exp (Real.exp ((7/10 : ℝ)*Z)))
    (hsmooth' : (largestPrimeFactor t.remainder : ℝ)≤Real.exp (Real.exp ((7/10 : ℝ)*Z))) :
    ∀ r, |leftFactorHeight t r-rightFactorHeight t r| ≤
      (2*(r.val : ℝ)+1)*Real.sqrt (B S*B y) := by
  have ho := height_bounds_factor_order hZ ht
  apply ordered_largest_factor_alignment_smooth_cutoff t.left t.right hS hSZ hD hD'
    (fun r => (hnorm r).1) (fun r => (hnorm r).2) heq hsmooth hsmooth'
    (fun r => (ho.1 r).le) (fun r s hrs => (ho.2 r s hrs).le)
  intro r
  have hb : B (max (largestPrimeFactor (t.left r-1) : ℝ)
      (largestPrimeFactor (t.right r-1) : ℝ)) ≤ B y := by
    rcases le_total (largestPrimeFactor (t.left r-1) : ℝ) (largestPrimeFactor (t.right r-1) : ℝ) with h | h
    · simpa only [max_eq_right h,rightFactorHeight] using (ht.top r).2
    · simpa only [max_eq_left h,leftFactorHeight] using (ht.top r).1
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hb hBS)

/-- The concrete good collision lists are aligned also when their first
unequal prime is index zero. No extra comparison input is used. -/
theorem actual_surviving_alignment : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → p.Prime →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ →
    tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ) →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i →
    (∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) → ∀ y : ℝ,
    1<y → 0<B y → (87/100 : ℝ)*fordBandScale x i≤B y → B y≤2*fordBandScale x i →
    y^(9/10 : ℝ)≤wholeWitnessPrime p η i → y^(9/10 : ℝ)≤wholeWitnessPrime q ξ i →
    (∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 : ℕ)≤y ∧
      ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 : ℕ)≤y) →
    ∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      |leftFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)) r-
        rightFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)) r| ≤
        (2*(r.val : ℝ)+1)*Real.sqrt (B (normalityScale x i)*B y) := by
  filter_upwards [actual_surviving_geometry,collision_normality_domain,
    collision_normality_below_cutoff,collision_residual_below_cutoff,eventually_collision_indices]
    with H hgeom hdom hnorm hres hind
  filter_upwards [hgeom,hdom,hnorm,hres,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hg hd hn hr hm hBx
  intro i p q hi hL hR hp η ξ hη hξ hgη hgξ heq hfirst hcommon y hy hBy hByl hByu hpmin hqmin hsize
  have him : i < m x := hi.trans_lt (hR.trans hL)
  have hbi := fordBandScale_pos (zero_lt_one.trans hBx) him
  have hhalf : fordBandScale x i/2≤B y := by linarith
  have hk := (hind x hm i hi).2.2
  have hkm := hk.trans hL
  have hbk := fordBandScale_pos (zero_lt_one.trans hBx) hkm
  have hd0 := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := collisionLastIndex x i))
  have hd1 := Nat.totient_pos.mpr (suffixPreimage_pos hξ (i := collisionLastIndex x i))
  obtain ⟨_,ht⟩ := hg i p q hi η ξ hη hξ hgη hgξ hfirst y hy hBy hByl hByu hpmin hqmin hsize
  obtain ⟨hSb,hBS,_⟩ := hd i hi y hy hhalf
  apply alignment_of_height_bounds (lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hSb) (by linarith) (hn i hi).le hbk ht hd0.ne' hd1.ne'
    (fun r => ⟨(surviving_good_conditions hi hgη hgξ r).1,
      (surviving_good_conditions hi hgη hgξ r).2.1⟩)
    (surviving_collision_identity hη hξ hp hL hR hk (Nat.le_add_right _ _) heq hfirst hcommon)
    (hr i hi η hη).le (hr i hi ξ hξ).le

end TotientAsymptotic

end

end OAI
