import OAI.NumberTheory.TotientAsymptotic.SurvivingHeights
import OAI.NumberTheory.TotientAsymptotic.SurvivingGridGeometry

namespace OAI

/-! Height geometry derived from the chosen actual good witnesses. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def leftFactorHeight {b : ℕ} (t : ShiftedPair b) (r : Fin b) : ℝ :=
  B (largestPrimeFactor (t.left r-1))

def rightFactorHeight {b : ℕ} (t : ShiftedPair b) (r : Fin b) : ℝ :=
  B (largestPrimeFactor (t.right r-1))

structure ComparisonHeightBounds {b : ℕ} (t : ShiftedPair b) (Y Z : ℝ) : Prop where
  positive : ∀ r, 0 < leftFactorHeight t r ∧ 0 < rightFactorHeight t r
  top : ∀ r, leftFactorHeight t r ≤ Y ∧ rightFactorHeight t r ≤ Y
  head : ∀ hb : 0<b, (9/10 : ℝ)*Y ≤ min (leftFactorHeight t ⟨0,hb⟩) (rightFactorHeight t ⟨0,hb⟩)
  tail : ∀ r, 0<r.val → max (leftFactorHeight t r) (rightFactorHeight t r) ≤ (18/25 : ℝ)*Y
  bottom : ∀ r, (4/5 : ℝ)*Z ≤ min (leftFactorHeight t r) (rightFactorHeight t r)
  separated : ∀ r s, r<s → (1/10 : ℝ)*Z ≤
    min (leftFactorHeight t r) (rightFactorHeight t r)-max (leftFactorHeight t s) (rightFactorHeight t s)

/-- Both the zero and positive first-difference cases have the same concrete
height geometry at their counting endpoint. -/
theorem actual_surviving_geometry : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, i ≤ R x H →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i → ∀ y : ℝ,
    1<y → 0<B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
    y^(9/10 : ℝ) ≤ wholeWitnessPrime p η i → y^(9/10 : ℝ) ≤ wholeWitnessPrime q ξ i →
    (∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 : ℕ) ≤ y ∧
      ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 : ℕ) ≤ y) →
    0<(collisionSurvivors p q η ξ i (collisionLastIndex x i)).card ∧
      ComparisonHeightBounds (survivingPair p q η ξ i (collisionLastIndex x i))
        (B y) (fordBandScale x (collisionLastIndex x i)) := by
  filter_upwards [surviving_factor_heights,eventually_collision_indices,eventually_ge_atTop 4]
    with H hheights hind hH
  filter_upwards [hheights,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hx hm hBx
  intro i p q hi η ξ hη hξ hgη hgξ hfirst y hy hBy hByl hByu hpmin hqmin hsize
  have him : i < m x := by unfold R at hi; omega
  have hhalf : fordBandScale x i/2 ≤ B y := by
    have hb := fordBandScale_pos (zero_lt_one.trans hBx) him
    linarith
  obtain ⟨hb,hhead,hheight,hbands⟩ := hx i p q hi η ξ hη hξ hgη hgξ hfirst y hy hBy hhalf hByu hpmin hqmin hsize
  obtain ⟨hHi,hcut,hkL⟩ := hind x hm i hi
  have hk : collisionLastIndex x i < m x := hkL.trans_le (Nat.sub_le _ _)
  obtain ⟨hb',hidx0⟩ := survivingIndex_first (Nat.le_add_right i _) hfirst
  change survivingIndex p q η ξ i (collisionLastIndex x i) ⟨0,hb'⟩=i at hidx0
  have hidx (r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card) :
      survivingIndex p q η ξ i (collisionLastIndex x i) r ≤ collisionLastIndex x i :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (survivingIndex_mem p q η ξ i (collisionLastIndex x i) r)).1).2
  have hmin : (9/10 : ℝ)*B y ≤ min
      (leftFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)) ⟨0,hb⟩)
      (rightFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)) ⟨0,hb⟩) := le_min hhead.1 hhead.2
  obtain ⟨htail,hbottom,hsep⟩ := ordered_surviving_band_margins hb hBx him hk
    (survivingIndex p q η ξ i (collisionLastIndex x i)) hidx0 hidx hBy hByl
    (collision_last_band_le_half hBx him (by omega) hcut)
    (leftFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)))
    (rightFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i))) hmin
    (fun r hr => le_min (hbands r hr).1.1 (hbands r hr).2.1)
    (fun r hr => max_le (hbands r hr).1.2 (hbands r hr).2.2)
  refine ⟨hb,⟨?_,?_,?_,htail,hbottom,hsep⟩⟩
  · intro r
    exact ⟨(hheight r).1.1,(hheight r).2.1⟩
  · intro r
    exact ⟨(hheight r).1.2,(hheight r).2.2⟩
  · intro hb''
    exact hmin

end TotientAsymptotic

end

end OAI
