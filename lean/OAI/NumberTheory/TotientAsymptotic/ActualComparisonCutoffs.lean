import OAI.NumberTheory.TotientAsymptotic.ComparisonGridFromHeights
import OAI.NumberTheory.TotientAsymptotic.HeightAlignment
import OAI.NumberTheory.TotientAsymptotic.SurvivingBlockSize
import OAI.NumberTheory.TotientAsymptotic.SurvivingAlignment

namespace OAI

/-! Explicit finite cutoffs for the actual collision comparison. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def pairGridLabel {b : ℕ} (t : ShiftedPair b) (y δ : ℝ) (r : Fin b) : ℕ :=
  collisionGridIndex δ (leftFactorHeight t r/B y) (rightFactorHeight t r/B y)

def pairUpperCoordinates {b : ℕ} (t : ShiftedPair b) (y Z δ : ℝ) : ℕ → ℝ :=
  pairedGridUpper δ ((7/10 : ℝ)*Z/B y) (pairGridLabel t y δ)

def pairLowerCoordinates {b : ℕ} (t : ShiftedPair b) (y δ : ℝ) : ℕ → ℝ :=
  pairedGridLower δ (pairGridLabel t y δ)

lemma exp_exp_doubleLog {w : ℝ} (hw : 1< w) : Real.exp (Real.exp (B w))=w := by
  rw [B,Real.exp_log (Real.log_pos hw),Real.exp_log (zero_lt_one.trans hw)]

lemma comparisonCutoffs_interval {y w l u : ℝ} (hBy : 0< B y) (hw : 1< w)
    (hl : l≤ B w/B y) (hu : B w/B y≤ u) :
    Real.exp (Real.exp (B y*l))≤ w ∧ w≤ Real.exp (Real.exp (B y*u)) := by
  have hl' := (le_div_iff₀ hBy).mp hl
  have hu' := (div_le_iff₀ hBy).mp hu
  constructor
  · rw [← exp_exp_doubleLog hw]
    exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith))
  · rw [← exp_exp_doubleLog hw]
    exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith))

/-- The normalized grid constructed from a collision has all of Ford's
parameter restrictions. The small integer bounds are precisely the previously
proved residual and canceled-product size conclusions. -/
theorem actual_comparison_parameters : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, i≤ R x H → L x H< m x → R x H< L x H → p.Prime →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ →
    tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ) →
    wholeWitnessPrime p η i≠wholeWitnessPrime q ξ i →
    (∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) → ∀ y : ℝ,
    1< y → 0< B y → (87/100 : ℝ)*fordBandScale x i≤ B y → B y≤2*fordBandScale x i →
    y^(9/10 : ℝ)≤ wholeWitnessPrime p η i → y^(9/10 : ℝ)≤ wholeWitnessPrime q ξ i →
    (witnessBlockValue p η i (collisionLastIndex x i) : ℝ)≤ y →
    (collisionResidual η i : ℝ)≤ y^(1/100 : ℝ) →
    (collisionCanceledProduct p q η ξ i (collisionLastIndex x i) : ℝ)≤ y^(1/10 : ℝ) →
    let t := survivingPair p q η ξ i (collisionLastIndex x i)
    let Z := fordBandScale x (collisionLastIndex x i)
    let δ := collisionMesh x y i
    let U := comparisonCutoffs y (pairLowerCoordinates t y δ)
    let Y := comparisonCutoffs y (pairUpperCoordinates t y Z δ)
    pairGridLabel t y δ∈collisionGridFamilies δ (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card ∧
    FordComparisonParameters (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
      y (normalityScale x i) (collisionResidual η i)
      (collisionCanceledProduct p q η ξ i (collisionLastIndex x i)) Y U ∧
    FordComparisonConditions (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
      y (normalityScale x i) (collisionResidual η i)
      (collisionCanceledProduct p q η ξ i (collisionLastIndex x i)) Y U t := by
  filter_upwards [actual_surviving_geometry,actual_surviving_alignment,collisionMesh_bound,
    collision_normality_domain,collision_normality_below_cutoff,collision_residual_below_cutoff,eventually_collision_indices,
    collision_endpoints_eventually ford_parameters_of_normalized_grid,
    collision_endpoints_eventually surviving_comparison_conditions,eventually_ge_atTop 4]
    with H hgeom halign hmesh hdomain hScut hres hind hparam hcond hH
  filter_upwards [hgeom,halign,hmesh,hdomain,hScut,hres,hparam,hcond,
    m_tendsto.eventually (eventually_ge_atTop H),B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))]
    with x hg ha hd hdom hSc hres hp hc hm hBx
  intro i p q hi hL hR hprime η ξ hη hξ hgη hgξ heq hfirst hcommon y hy hBy hByl hByu hpmin hqmin hsize hDy hry
  dsimp only
  let t := survivingPair p q η ξ i (collisionLastIndex x i)
  let b := (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
  let Z := fordBandScale x (collisionLastIndex x i)
  let δ := collisionMesh x y i
  have him : i< m x := hi.trans_lt (hR.trans hL)
  have hbi := fordBandScale_pos (zero_lt_one.trans hBx) him
  have hhalf : fordBandScale x i/2≤ B y := by linarith
  obtain ⟨hHi,hcut,hkL⟩ := hind x hm i hi
  have hk : collisionLastIndex x i< m x := hkL.trans hL
  have hZ : 0< Z := fordBandScale_pos (zero_lt_one.trans hBx) hk
  have hh : 4≤ m x-i := hH.trans hHi
  have hshift := surviving_shift_le_block hη hξ hprime hL hR hkL (Nat.le_add_right _ _) heq hfirst hcommon hsize
  obtain ⟨hb,ht⟩ := hg i p q hi η ξ hη hξ hgη hgξ hfirst y hy hBy hByl hByu hpmin hqmin hshift
  have hbcard : b≤ m x-i := by
    have hc := Finset.card_filter_le (Finset.Icc i (collisionLastIndex x i))
      (fun j => wholeWitnessPrime p η j≠wholeWitnessPrime q ξ j)
    change b≤_ at hc
    simp only [Nat.card_Icc] at hc
    unfold collisionLastIndex at hc
    omega
  have hδ : 0<δ := collisionMesh_pos hbi hBy
  have hδu : δ≤2/((m x-i : ℕ) : ℝ)^32 := hd i hi y hBy hhalf
  have hmargin : (2*((m x-i : ℕ) : ℝ)+10)*δ<(1/10 : ℝ)*Z/B y :=
    (collision_rounding_margin hh hδu).trans
      (normalized_factor_margin hh hBx him hcut rfl hBy hByu)
  have hZY : Z≤ B y := by
    have hl := collision_last_band_le_half hBx him (by omega) hcut
    exact hl.trans hhalf
  have hn := comparison_grid_from_heights hb hbcard hh hBy hZ hZY hδ hδu hmargin ht
    (fun r => normalized_alignment_bound hBy
      (ha i p q hi hL hR hprime η ξ hη hξ hgη hgξ heq hfirst hcommon y hy hBy hByl hByu hpmin hqmin hshift r))
  obtain ⟨hnmem,hν0,hνb,hinterval,horder,hν1,hgap⟩ := hn
  have hνb' : pairedGridUpper δ ((7/10 : ℝ)*Z/B y) (pairGridLabel t y δ) b=(7/10 : ℝ)*Z/B y := hνb
  obtain ⟨hS,hBS,hSy⟩ := hdom i hi y hy hhalf
  have hYb : comparisonCutoffs y (pairUpperCoordinates t y Z δ) b=collisionSmoothCutoff x i := by
    change Real.exp (Real.exp (B y*pairedGridUpper δ ((7/10 : ℝ)*Z/B y) (pairGridLabel t y δ) b))=_
    rw [hνb']
    congr 2
    change B y*((7/10 : ℝ)*Z/B y)=(7/10 : ℝ)*Z
    field_simp
  refine ⟨hnmem,?_,?_⟩
  · apply hp i hi y hy hhalf b (collisionResidual η i)
      (collisionCanceledProduct p q η ξ i (collisionLastIndex x i)) (normalityScale x i)
      (pairUpperCoordinates t y Z δ) (pairLowerCoordinates t y δ) hb hν0 hS
    · rw [hYb]
      exact (hSc i hi).le
    · exact horder
    · exact hν1.le
    · intro j hj
      rw [← collisionMesh_eq_sqrt_ratio (by linarith : 0≤ B (normalityScale x i))]
      exact hgap j hj
    · exact Nat.totient_pos.mpr (suffixPreimage_pos hη)
    · exact hDy
    · rw [hYb]
      exact (hres i hi η hη).le
    · exact collisionCanceledProduct_pos hη hprime hkL.le
    · exact hry
  · apply hc i hi y hy hhalf hη hξ hprime hL hR hi hkL heq hfirst hcommon hgη hgξ
      (comparisonCutoffs y (pairUpperCoordinates t y Z δ))
      (comparisonCutoffs y (pairLowerCoordinates t y δ))
      (lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hS)
      (by linarith) hSy hYb
    · intro r
      have hl := comparisonCutoffs_interval hBy
        (by exact_mod_cast one_lt_nat_of_doubleLog_pos (ht.positive r).1)
        (hinterval r).1 (hinterval r).2.2.1
      have hr := comparisonCutoffs_interval hBy
        (by exact_mod_cast one_lt_nat_of_doubleLog_pos (ht.positive r).2)
        (hinterval r).2.1 (hinterval r).2.2.2
      exact ⟨hl.1,hl.2,hr.1,hr.2⟩
    · exact hsize
    · exact (hres i hi ξ hξ).le
    · exact hpmin
    · exact (Real.one_lt_exp_iff.mpr (Real.exp_pos _)).le
    · apply Real.exp_le_exp.mpr
      apply Real.exp_le_exp.mpr
      have hν1' : pairUpperCoordinates t y Z δ 1 < 4/5 := hν1
      change B y*pairUpperCoordinates t y Z δ 1 ≤ (4/5 : ℝ)*B y
      nlinarith


end TotientAsymptotic

end

end OAI
