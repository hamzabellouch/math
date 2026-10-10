import OAI.NumberTheory.TotientAsymptotic.ActualGridSlack
import OAI.NumberTheory.TotientAsymptotic.CollisionCoordinateEndpoint

namespace OAI

/-! The strict exponent saving for every actual good collision block. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

theorem actual_collision_exponent : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → p.Prime →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ →
    tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ) →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i →
    (∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) → ∀ y : ℝ,
    1 < y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
    y^(9/10 : ℝ) ≤ wholeWitnessPrime p η i → y^(9/10 : ℝ) ≤ wholeWitnessPrime q ξ i →
    (witnessBlockValue p η i (collisionLastIndex x i) : ℝ) ≤ y → (i=0 → y=x) →
    let t := survivingPair p q η ξ i (collisionLastIndex x i)
    let b := (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
    let Z := fordBandScale x (collisionLastIndex x i)
    let δ := collisionMesh x y i
    let Y := comparisonCutoffs y (pairUpperCoordinates t y Z δ)
    let U := comparisonCutoffs y (pairLowerCoordinates t y δ)
    (-2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y))+
      comparisonError b y (normalityScale x i) Y U ≤ -1-1/(2*((m x-i : ℕ) : ℝ)^4)) := by
  filter_upwards [actual_surviving_geometry,actual_surviving_alignment,collision_normality_domain,
    collisionMesh_bound,eventually_collision_indices,eventually_ge_atTop 4]
    with H hgeom halign hdomain hmesh hind hH
  filter_upwards [hgeom,halign,hdomain,hmesh,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hg ha hd hmsh hm hBx
  intro i p q hi hL hR hp η ξ hη hξ hgη hgξ heq hfirst hcommon y hy hBy hByl hByu hpmin hqmin hsize hzero
  dsimp only
  have him : i < m x := hi.trans_lt (hR.trans hL)
  have hbi := fordBandScale_pos (zero_lt_one.trans hBx) him
  have hhalf : fordBandScale x i/2 ≤ B y := by linarith
  obtain ⟨hHi,_,hk⟩ := hind x hm i hi
  have hh : 2 ≤ m x-i := by omega
  have hshift := surviving_shift_le_block hη hξ hp hL hR hk (Nat.le_add_right _ _) heq hfirst hcommon hsize
  obtain ⟨_,ht⟩ := hg i p q hi η ξ hη hξ hgη hgξ hfirst y hy hBy hByl hByu hpmin hqmin hshift
  have hal := ha i p q hi hL hR hp η ξ hη hξ hgη hgξ heq hfirst hcommon y hy hBy hByl hByu hpmin hqmin hshift
  obtain ⟨hS,hBS,hSy⟩ := hd i hi y hy hhalf
  have hS1 : 1 < normalityScale x i := (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hBmono : B (normalityScale x i) ≤ B y :=
    Real.log_le_log (Real.log_pos hS1) (Real.log_le_log (zero_lt_one.trans hS1) hSy)
  have hBy1 : 1 ≤ B y := hBS.trans hBmono
  have hinv := inverse_le_collisionMesh hBS hBy1
  have hδ := collisionMesh_pos hbi hBy
  have hδu := hmsh i hi y hBy hhalf
  have hcoord : remainderCoord x η i ≤ B y+1 := by
    by_cases hi0 : i=0
    · have hyx := hzero hi0
      subst i
      subst y
      simp only [remainderCoord,ite_true]
      linarith
    · have hip : 1 ≤ i := by omega
      have hik : i ≤ collisionLastIndex x i := Nat.le_add_right _ _
      have hblock := hsize
      rw [witnessBlockValue_positive hη hL hip hik hk] at hblock
      have htail := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := i))
      have hle : remainderPrime η i-1 ≤ (remainderPrime η i-1)*(suffixPreimage η i).totient :=
        Nat.le_mul_of_pos_right _ htail
      have hpy : ((remainderPrime η i-1 : ℕ) : ℝ) ≤ y :=
        (show ((remainderPrime η i-1 : ℕ) : ℝ) ≤ ((remainderPrime η i-1)*(suffixPreimage η i).totient : ℕ) by
          exact_mod_cast hle).trans hblock
      have he : Real.exp 1 ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.mpr
        (by have := Real.add_one_le_exp (1 : ℝ); linarith)
      exact remainder_coordinate_endpoint_bound hη hL (Finset.mem_Icc.mpr ⟨hip,hik.trans hk.le⟩)
        (he.trans (hS.trans hSy)) hpy
  have hbcard : (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card ≤ m x-i := by
    have hc := Finset.card_filter_le (Finset.Icc i (collisionLastIndex x i))
      (fun j => wholeWitnessPrime p η j ≠ wholeWitnessPrime q ξ j)
    change (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card ≤ _ at hc
    simp only [Nat.card_Icc] at hc
    have hcalc : collisionLastIndex x i+1-i=collisionCutoff (m x-i)+1 := by
      unfold collisionLastIndex
      omega
    rw [hcalc] at hc
    have hcut := (hind x hm i hi).2.1
    omega
  exact actual_grid_exponent_saving hη hL hgη hi hk hfirst hh hBy hδ hδu hcoord hinv ht
    (fun r => normalized_alignment_bound hBy (hal r)) hbcard
    (collisionMesh_eq_sqrt_ratio (by linarith : 0 ≤ B (normalityScale x i))).symm

end TotientAsymptotic

end

end OAI
