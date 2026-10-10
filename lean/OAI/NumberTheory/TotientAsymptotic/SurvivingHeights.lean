import OAI.NumberTheory.TotientAsymptotic.CollisionFactorHeights
import OAI.NumberTheory.TotientAsymptotic.CollisionEndpointDomain
import OAI.NumberTheory.TotientAsymptotic.SurvivingCollision

namespace OAI

/-! Actual surviving factors, with uniform top and positive-coordinate bounds. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma one_lt_nat_of_doubleLog_pos {n : ℕ} (hn : 0 < B n) : 1<n := by
  by_contra! h
  interval_cases n <;> norm_num [B] at hn

/-- Unlike the positive-coordinate band lemma, this also covers collisions
whose first different prime is the largest prime of the tuple. -/
theorem surviving_factor_heights : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, i ≤ R x H →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i → ∀ y : ℝ,
    1<y → 0<B y → fordBandScale x i/2 ≤ B y → B y ≤ 2*fordBandScale x i →
    y^(9/10 : ℝ) ≤ wholeWitnessPrime p η i → y^(9/10 : ℝ) ≤ wholeWitnessPrime q ξ i →
    (∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 : ℕ) ≤ y ∧
      ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 : ℕ) ≤ y) →
    ∃ hb : 0<(collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      ((9/10 : ℝ)*B y ≤ B (largestPrimeFactor
        ((survivingPair p q η ξ i (collisionLastIndex x i)).left ⟨0,hb⟩-1)) ∧
       (9/10 : ℝ)*B y ≤ B (largestPrimeFactor
        ((survivingPair p q η ξ i (collisionLastIndex x i)).right ⟨0,hb⟩-1))) ∧
      (∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
        (0 < B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ∧
         B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ≤ B y) ∧
        (0 < B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ∧
         B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ≤ B y)) ∧
      (∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card, 0<r.val →
        ((22/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r) ≤
          B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ∧
         B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ≤
          (28/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r)) ∧
        ((22/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r) ≤
          B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ∧
         B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ≤
          (28/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r))) := by
  filter_upwards [collision_factor_ford_bands,collision_normality_domain,
    collision_endpoints_eventually normal_head_largest_factor,eventually_collision_indices]
    with H hband hdomain hhead hind
  filter_upwards [hband,hdomain,hhead,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hband hdomain hhead hm hBx
  intro i p q hi η ξ hη hξ hgη hgξ hfirst y hy hBy hByl hByu hpmin hqmin hsize
  obtain ⟨hb,hidx0⟩ := survivingIndex_first (Nat.le_add_right i _) hfirst
  change 0 < (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card at hb
  change survivingIndex p q η ξ i (collisionLastIndex x i) ⟨0,hb⟩=i at hidx0
  have hk := (hind x hm i hi).2.2
  have hgood := surviving_good_conditions hi hgη hgξ
  obtain ⟨hSbig,hBS,hSy⟩ := hdomain i hi y hy hByl
  have hS : 1 < normalityScale x i :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hSbig
  have hBS0 : 0 ≤ B (normalityScale x i) := by linarith
  have hheadfun := hhead i hi y hy hByl
  have hfirstp : (survivingPair p q η ξ i (collisionLastIndex x i)).left ⟨0,hb⟩ = wholeWitnessPrime p η i := by
    simp only [survivingPair,hidx0]
  have hfirstq : (survivingPair p q η ξ i (collisionLastIndex x i)).right ⟨0,hb⟩ = wholeWitnessPrime q ξ i := by
    simp only [survivingPair,hidx0]
  have hl := hheadfun _ _ (hgood ⟨0,hb⟩).1 hS hBS0 hSy
    (by simpa only [hfirstp] using hpmin) (hsize ⟨0,hb⟩).1
  have hr := hheadfun _ _ (hgood ⟨0,hb⟩).2.1 hS hBS0 hSy
    (by simpa only [hfirstq] using hqmin) (hsize ⟨0,hb⟩).2
  have hpositive (r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card)
      (hr0 : 0<r.val) :
      ((22/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r) ≤
        B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ∧
       B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ≤
        (28/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r)) ∧
      ((22/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r) ≤
        B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ∧
       B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ≤
        (28/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r)) := by
    have hlt : i < survivingIndex p q η ξ i (collisionLastIndex x i) r := by
      calc
        i = survivingIndex p q η ξ i (collisionLastIndex x i) ⟨0,hb⟩ := hidx0.symm
        _ < _ := (survivingIndex p q η ξ i (collisionLastIndex x i)).strictMono hr0
    have hj := (Finset.mem_Icc.mp (Finset.mem_filter.mp
      (survivingIndex_mem p q η ξ i (collisionLastIndex x i) r)).1).2
    have hj0 : survivingIndex p q η ξ i (collisionLastIndex x i) r ≠ 0 := by omega
    have hbη := hband i hi _ (Finset.mem_Icc.mpr ⟨by omega,hj⟩) (hj.trans hk.le)
      η hη y hS hBS0 hSy hBy hByu
    have hbξ := hband i hi _ (Finset.mem_Icc.mpr ⟨by omega,hj⟩) (hj.trans hk.le)
      ξ hξ y hS hBS0 hSy hBy hByu
    have hg := hgood r
    have hs := hsize r
    simp only [survivingPair,wholeWitnessPrime,ite_eq_right hj0] at hg hs ⊢
    exact ⟨hbη hg.1 hs.1,hbξ hg.2.1 hs.2⟩
  refine ⟨hb,⟨hl,hr⟩,?_,hpositive⟩
  intro r
  have hpos : 0 < B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ∧
      0 < B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) := by
    by_cases hr0 : r.val=0
    · have he : r=⟨0,hb⟩ := Fin.ext hr0
      subst r
      exact ⟨(mul_pos (by norm_num) hBy).trans_le hl,(mul_pos (by norm_num) hBy).trans_le hr⟩
    · have hj := (Finset.mem_Icc.mp (Finset.mem_filter.mp
        (survivingIndex_mem p q η ξ i (collisionLastIndex x i) r)).1).2
      have hjm := (hj.trans_lt hk).trans_le (Nat.sub_le _ _)
      have hbp := fordBandScale_pos (zero_lt_one.trans hBx) hjm
      exact ⟨(mul_pos (by norm_num) hbp).trans_le (hpositive r (by omega)).1.1,
        (mul_pos (by norm_num) hbp).trans_le (hpositive r (by omega)).2.1⟩
  have hupper (n : ℕ) (hn : 0<B n) (hmn : (n : ℝ)≤y) : B n≤B y := by
    have hn1 : (1 : ℝ)<n := by exact_mod_cast one_lt_nat_of_doubleLog_pos hn
    exact Real.log_le_log (Real.log_pos hn1)
      (Real.log_le_log (zero_lt_one.trans hn1) hmn)

  constructor
  · refine ⟨hpos.1,hupper _ hpos.1 ?_⟩
    have hn : 1≤(survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 := by
      have := (hgood r).1.1.two_le
      omega
    exact (show (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1) : ℝ) ≤
      ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 : ℕ) by
      exact_mod_cast largestPrimeFactor_le_self hn).trans (hsize r).1
  · refine ⟨hpos.2,hupper _ hpos.2 ?_⟩
    have hn : 1≤(survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 := by
      have := (hgood r).2.1.1.two_le
      omega
    exact (show (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1) : ℝ) ≤
      ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 : ℕ) by
      exact_mod_cast largestPrimeFactor_le_self hn).trans (hsize r).2

end TotientAsymptotic

end

end OAI
