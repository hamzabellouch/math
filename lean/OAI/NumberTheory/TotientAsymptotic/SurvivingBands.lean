import OAI.NumberTheory.TotientAsymptotic.NormalFactorBands
import OAI.NumberTheory.TotientAsymptotic.SurvivingCollision

namespace OAI

/-! Strict ordering of the actual surviving largest factors and their cutoff. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma lt_of_doubleLog_lt {u v : ℝ} (_hu : 1 < u) (hv : 1 < v) (h : B u < B v) : u < v := by
  by_contra! hle
  have hh := Real.log_le_log (Real.log_pos hv) (Real.log_le_log (zero_lt_one.trans hv) hle)
  exact (not_le_of_gt h) hh

/-- The bands used to align the collision primes are disjoint even after the
normality losses, and all lie above the smooth-residual cutoff. -/
theorem surviving_largest_factor_bands : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, 1 ≤ i → i ≤ R x H → L x H < m x →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ → ∀ y : ℝ,
    1 < normalityScale x i → 0 ≤ B (normalityScale x i) → normalityScale x i ≤ y →
    0 < B y → B y ≤ 2*fordBandScale x i →
    (∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 : ℕ) ≤ y ∧
      ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 : ℕ) ≤ y) →
    (∀ r, collisionSmoothCutoff x i <
      min (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1) : ℝ)
        (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1) : ℝ)) ∧
    (∀ r s, r < s →
      max (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left s-1) : ℝ)
        (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right s-1) : ℝ) <
      min (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1) : ℝ)
        (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1) : ℝ)) := by
  filter_upwards [collision_normal_factor_bands,eventually_collision_indices] with H hband hind
  filter_upwards [hband,m_tendsto.eventually (eventually_ge_atTop H),
    fordBandScale_uniform_comparison (ε := 1/100) (by norm_num)] with x hx hm hcompare
  intro i p q hi hiR hL η ξ hη hξ hgη hgξ y hS hBS hSy hBy hByu hsize
  have hk := (hind x hm i hiR).2.2
  have hkm : collisionLastIndex x i < m x := hk.trans hL
  have hindmem (r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card) :
      survivingIndex p q η ξ i (collisionLastIndex x i) r ∈ Finset.Icc 1 (collisionLastIndex x i) := by
    have hh := (Finset.mem_filter.mp (survivingIndex_mem p q η ξ i (collisionLastIndex x i) r)).1
    exact Finset.mem_Icc.mpr ⟨hi.trans (Finset.mem_Icc.mp hh).1,(Finset.mem_Icc.mp hh).2⟩
  have hgood := surviving_good_conditions hiR hgη hgξ
  have hindexL (r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card) :
      survivingIndex p q η ξ i (collisionLastIndex x i) r ≤ L x H :=
    (Finset.mem_Icc.mp (hindmem r)).2.trans hk.le
  have hn0 (r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card) :
      survivingIndex p q η ξ i (collisionLastIndex x i) r ≠ 0 := by
    have := (Finset.mem_Icc.mp (hindmem r)).1
    omega
  have hbds (r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card) :
      ((89/100 : ℝ)*bandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r) ≤
        B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ∧
      B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ≤
        (11/10 : ℝ)*bandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r)) ∧
      ((89/100 : ℝ)*bandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r) ≤
        B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ∧
      B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ≤
        (11/10 : ℝ)*bandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r)) := by
    have hl := hx i hiR _ (hindmem r) (hindexL r) η hη y hS hBS hSy hBy hByu
    have hr := hx i hiR _ (hindmem r) (hindexL r) ξ hξ y hS hBS hSy hBy hByu
    simpa only [survivingPair,wholeWitnessPrime,ite_eq_right (hn0 r)] using
      And.intro (hl (by simpa only [survivingPair,wholeWitnessPrime,ite_eq_right (hn0 r)] using (hgood r).1)
        (by simpa only [survivingPair,wholeWitnessPrime,ite_eq_right (hn0 r)] using (hsize r).1))
      (hr (by simpa only [survivingPair,wholeWitnessPrime,ite_eq_right (hn0 r)] using (hgood r).2.1)
        (by simpa only [survivingPair,wholeWitnessPrime,ite_eq_right (hn0 r)] using (hsize r).2))
  have hpos (r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card) :
      (1 : ℝ) < largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1) ∧
      (1 : ℝ) < largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1) := by
    have hj := hindmem r
    have hjm := (Finset.mem_Icc.mp hj).2.trans_lt hkm
    have hl := basic_remainder_prime_ge_three hη
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,hindexL r⟩) hjm
    have hr := basic_remainder_prime_ge_three hξ
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,hindexL r⟩) hjm
    simp only [survivingPair,wholeWitnessPrime,ite_eq_right (hn0 r)]
    exact ⟨by exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ remainderPrime η _-1 by omega),
      by exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ remainderPrime ξ _-1 by omega)⟩
  constructor
  · intro r
    have hb := bandScale_pos hkm
    have hf : fordBandScale x (collisionLastIndex x i) ≤
        (101/100 : ℝ)*bandScale x (collisionLastIndex x i) := by
      apply le_of_lt
      apply (div_lt_iff₀ hb).mp
      linarith [(abs_lt.mp (hcompare _ hkm)).2]
    have hmono := bandScale_antitone x (Finset.mem_Icc.mp (hindmem r)).2
    have hZ : 1 < collisionSmoothCutoff x i := Real.one_lt_exp_iff.mpr (Real.exp_pos _)
    have hBZ : B (collisionSmoothCutoff x i) = (7/10 : ℝ)*fordBandScale x (collisionLastIndex x i) := by
      simp only [collisionSmoothCutoff,B,Real.log_exp]
    apply lt_min
    · apply lt_of_doubleLog_lt hZ (hpos r).1
      rw [hBZ]
      nlinarith [(hbds r).1.1]
    · apply lt_of_doubleLog_lt hZ (hpos r).2
      rw [hBZ]
      nlinarith [(hbds r).2.1]
  · intro r s hrs
    have hidx := (survivingIndex p q η ξ i (collisionLastIndex x i)).strictMono hrs
    have hsep := separated_normal_factor_bands hidx
      ((Finset.mem_Icc.mp (hindmem r)).2.trans_lt hkm)
    apply max_lt
    · apply lt_min
      · exact lt_of_doubleLog_lt (hpos s).1 (hpos r).1
          (((hbds s).1.2.trans_lt hsep).trans_le (hbds r).1.1)
      · exact lt_of_doubleLog_lt (hpos s).1 (hpos r).2
          (((hbds s).1.2.trans_lt hsep).trans_le (hbds r).2.1)
    · apply lt_min
      · exact lt_of_doubleLog_lt (hpos s).2 (hpos r).1
          (((hbds s).2.2.trans_lt hsep).trans_le (hbds r).1.1)
      · exact lt_of_doubleLog_lt (hpos s).2 (hpos r).2
          (((hbds s).2.2.trans_lt hsep).trans_le (hbds r).2.1)

end TotientAsymptotic

end

end OAI
