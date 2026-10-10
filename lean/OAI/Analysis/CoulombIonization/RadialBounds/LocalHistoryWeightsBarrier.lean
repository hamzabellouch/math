import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.LocalFieldEnvelopeBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open scoped BigOperators

def localizationIMSConstant : ℝ := (3/2:ℝ)*(Real.pi*smoothTransitionBound)^2
lemma localizationIMSConstant_nonneg : 0 ≤ localizationIMSConstant := by
  unfold localizationIMSConstant
  positivity

lemma localHistoryRadius_recip {a : ℝ} (ha : 0 < a) (n : ℕ) :
    1/localHistoryRadius a n ≤ ((n:ℝ)+2)^2/a := by
  have he : 1/localHistoryRadius a n = (((n:ℝ)+1)*((n:ℝ)+2))/a := by
    unfold localHistoryRadius
    field_simp
  rw [he]
  apply div_le_div_of_nonneg_right _ ha.le
  have : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith

lemma localHistoryRadius_fourth {a : ℝ} (ha : 0 < a) (n : ℕ) :
    1/(localHistoryRadius a n)^4 ≤ ((n:ℝ)+2)^8/a^4 := by
  have := localHistoryRadius_pos ha n
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/localHistoryRadius a n)
    (localHistoryRadius_recip ha n) 4
  simpa only [div_pow,one_pow,←pow_mul] using hh

lemma localHistoryRadius_second {a : ℝ} (ha : 0 < a) (n : ℕ) :
    1/(localHistoryRadius a n)^2 ≤ ((n:ℝ)+2)^4/a^2 := by
  have := localHistoryRadius_pos ha n
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/localHistoryRadius a n)
    (localHistoryRadius_recip ha n) 2
  simpa only [div_pow,one_pow,←pow_mul] using hh

lemma localHistoryRadius_packet {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (1/(localHistoryRadius a n)^4+1/localHistoryRadius a n)^2 ≤
      (1/a^4+1/a)^2*((n:ℝ)+2)^16 := by
  have hw : 1 ≤ (n:ℝ)+2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hp : ((n:ℝ)+2)^2 ≤ ((n:ℝ)+2)^8 := pow_le_pow_right₀ hw (by norm_num)
  have hi := (localHistoryRadius_recip ha n).trans (div_le_div_of_nonneg_right hp ha.le)
  have hu := add_le_add (localHistoryRadius_fourth ha n) hi
  have hn : 0 ≤ 1/(localHistoryRadius a n)^4+1/localHistoryRadius a n := by
    have := localHistoryRadius_pos ha n
    positivity
  have hh := pow_le_pow_left₀ hn hu 2
  calc (1/(localHistoryRadius a n)^4+1/localHistoryRadius a n)^2 ≤
      (((n:ℝ)+2)^8/a^4+((n:ℝ)+2)^8/a)^2 := hh
    _ = (1/a^4+1/a)^2*((n:ℝ)+2)^16 := by ring

lemma localHistoryRadius_ims {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (3/2:ℝ)*(Real.pi*smoothTransitionBound/localHistoryRadius a n)^2 ≤
      (localizationIMSConstant/a^2)*((n:ℝ)+3)^8 := by
  have h1 := mul_le_mul_of_nonneg_left (localHistoryRadius_second ha n) localizationIMSConstant_nonneg
  have hw : ((n:ℝ)+2)^4 ≤ ((n:ℝ)+3)^8 :=
    (pow_le_pow_left₀ (by positivity) (by linarith : (n:ℝ)+2 ≤ (n:ℝ)+3) 4).trans
      (pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num))
  have h2 := mul_le_mul_of_nonneg_left hw (div_nonneg localizationIMSConstant_nonneg (sq_nonneg a))
  calc (3/2:ℝ)*(Real.pi*smoothTransitionBound/localHistoryRadius a n)^2 =
      localizationIMSConstant*(1/localHistoryRadius a n^2) := by unfold localizationIMSConstant; ring
    _ ≤ localizationIMSConstant*(((n:ℝ)+2)^4/a^2) := h1
    _ = (localizationIMSConstant/a^2)*((n:ℝ)+2)^4 := by ring
    _ ≤ (localizationIMSConstant/a^2)*((n:ℝ)+3)^8 := h2

lemma localHistoryRadius_energy {a δ C : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hC : 0 ≤ C) (n : ℕ) :
    (δ+C*((n:ℝ)+1)*((n:ℝ)+3)^8)/localHistoryRadius a n ≤
      (δ/a+256*C/a)*((n:ℝ)+2)^16 := by
  let w : ℝ := (n:ℝ)+2
  have hw : 1 ≤ w := by dsimp [w]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw
  have hn : 0 ≤ (n:ℝ)+1 := by positivity
  have hnw : (n:ℝ)+1 ≤ w := by dsimp [w]; linarith
  have hn3 : (n:ℝ)+3 ≤ 2*w := by dsimp [w]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hpow : ((n:ℝ)+3)^8 ≤ 256*w^8 := by
    simpa only [mul_pow,show (2:ℝ)^8 = 256 by norm_num] using pow_le_pow_left₀ (by positivity) hn3 8
  have hp : C*((n:ℝ)+1)*((n:ℝ)+3)^8 ≤ 256*C*w^9 := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hnw hC) hpow (by positivity) (mul_nonneg hC hw0)
    calc C*((n:ℝ)+1)*((n:ℝ)+3)^8 ≤ (C*w)*(256*w^8) := h
      _ = 256*C*w^9 := by ring
  have hE := mul_le_mul (add_le_add le_rfl hp) (localHistoryRadius_recip ha n)
    (by have := localHistoryRadius_pos ha n; positivity) (by positivity : 0 ≤ δ+256*C*w^9)
  have hp2 : w^2 ≤ w^16 := pow_le_pow_right₀ hw (by norm_num)
  have hp11 : w^11 ≤ w^16 := pow_le_pow_right₀ hw (by norm_num)
  have h2 := mul_le_mul_of_nonneg_left hp2 (div_nonneg hδ ha.le)
  have h11 := mul_le_mul_of_nonneg_left hp11 (div_nonneg (by positivity : 0 ≤ 256*C) ha.le)
  calc (δ+C*((n:ℝ)+1)*((n:ℝ)+3)^8)/localHistoryRadius a n ≤
      (δ+256*C*w^9)*(w^2/a) := by simpa only [div_eq_mul_inv,one_mul] using hE
    _ = δ/a*w^2+(256*C/a)*w^11 := by ring
    _ ≤ δ/a*w^16+(256*C/a)*w^16 := add_le_add h2 h11
    _ = (δ/a+256*C/a)*((n:ℝ)+2)^16 := by dsimp [w]; ring

open Set Metric

def localHistoryCostScale (a B H : ℝ) : ℝ := (localizationIMSConstant/a^2+8*H)*Real.sqrt B
lemma localHistoryCostScale_nonneg (a B : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    0 ≤ localHistoryCostScale a B H := by
  unfold localHistoryCostScale
  exact mul_nonneg (add_nonneg (div_nonneg localizationIMSConstant_nonneg (sq_nonneg a)) (by positivity))
    (Real.sqrt_nonneg _)

lemma localHistory_excess_step {E₀ E : CoreObservationEnsemble} {y₀ : Space} {a Z lam : ℝ}
    {ha : 0 < a} (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    {n : ℕ} (hE : CoreLocalHistory E₀ y₀ a ha n E) (y : Space)
    (hy : y ∈ closedBall y₀ (localHistoryReach a n)) :
    (E.observe (coreFirstRadialCut y (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (localHistoryRadius_pos ha n).le)
      (localHistoryRadius_pos ha n))
      (coreFirstRadialCut_partition y (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (localHistoryRadius_pos ha n).le)
        (localHistoryRadius_pos ha n))).excess Z lam ≤ E.excess Z lam+
        localHistoryCostScale a (E₀.countMoment y₀ (8*a)) (localFieldEnvelope E₀ y₀ a ha Z lam)*((n:ℝ)+3)^8 := by
  have hH := localFieldEnvelope_nonneg E₀ y₀ ha hsep hm hZ hlam
  have hu := localHistoryRadius_pos ha n
  have hn := CoreLocalHistory.center_nuclear_separation (ha := ha) hsep y hy
  have hu' := localHistoryRadius_le ha n
  have hh := E.observe_excess_budget y (by positivity : 0 ≤ 2*localHistoryRadius a n) hu
    (by linarith : 2*localHistoryRadius a n+2*localHistoryRadius a n ≤ ‖y‖)
    (by linarith : 2*localHistoryRadius a n+localHistoryRadius a n < 4*localHistoryRadius a n) hZ hlam
  rw [hE.mass,hm,Real.sqrt_one,mul_one] at hh
  have hc := Real.sqrt_le_sqrt (hE.countMoment_local y hy)
  have hi := mul_le_mul (localHistoryRadius_ims ha n) hc (Real.sqrt_nonneg _)
    (mul_nonneg (div_nonneg localizationIMSConstant_nonneg (sq_nonneg a)) (by positivity))
  have ho := mul_le_mul (localFieldEnvelope_outMoment hsep hm hZ hlam hE y hy) hc
    (Real.sqrt_nonneg _) (by positivity)
  calc _ ≤ E.excess Z lam+((3/2:ℝ)*(Real.pi*smoothTransitionBound/localHistoryRadius a n)^2)*
      Real.sqrt (E.countMoment y (4*localHistoryRadius a n))+
      Real.sqrt (E.outMoment y _ _ Z lam)*Real.sqrt (E.countMoment y (4*localHistoryRadius a n)) := hh
    _ ≤ E.excess Z lam+(localizationIMSConstant/a^2)*((n:ℝ)+3)^8*Real.sqrt (E₀.countMoment y₀ (8*a))+
      (8*localFieldEnvelope E₀ y₀ a ha Z lam*((n:ℝ)+3)^8)*Real.sqrt (E₀.countMoment y₀ (8*a)) :=
      add_le_add (add_le_add le_rfl hi) ho
    _ = _ := by unfold localHistoryCostScale; ring

lemma localHistory_excess_bound {E₀ E : CoreObservationEnsemble} {y₀ : Space} {a Z lam : ℝ}
    {ha : 0 < a} (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    {n : ℕ} (hE : CoreLocalHistory E₀ y₀ a ha n E) :
    E.excess Z lam ≤ E₀.excess Z lam+
      localHistoryCostScale a (E₀.countMoment y₀ (8*a)) (localFieldEnvelope E₀ y₀ a ha Z lam)*
        (n:ℝ)*((n:ℝ)+2)^8 := by
  have hC := localHistoryCostScale_nonneg a (E₀.countMoment y₀ (8*a))
    (localFieldEnvelope_nonneg E₀ y₀ ha hsep hm hZ hlam)
  induction hE with
  | initial => simp
  | @observe n E hE y hy ih =>
    have hh := localHistory_excess_step hsep hm hZ hlam hE y hy
    have hp : ((n:ℝ)+2)^8 ≤ ((n:ℝ)+3)^8 := pow_le_pow_left₀ (by positivity) (by linarith) 8
    have hmul := mul_le_mul_of_nonneg_left hp (mul_nonneg hC (Nat.cast_nonneg n))
    push_cast
    calc
      _ ≤ E.excess Z lam+localHistoryCostScale a (E₀.countMoment y₀ (8*a))
        (localFieldEnvelope E₀ y₀ a ha Z lam)*((n:ℝ)+3)^8 := hh
      _ ≤ (E₀.excess Z lam+localHistoryCostScale a (E₀.countMoment y₀ (8*a))
        (localFieldEnvelope E₀ y₀ a ha Z lam)*(n:ℝ)*((n:ℝ)+2)^8)+
        localHistoryCostScale a (E₀.countMoment y₀ (8*a)) (localFieldEnvelope E₀ y₀ a ha Z lam)*((n:ℝ)+3)^8 :=
        add_le_add ih le_rfl
      _ ≤ (E₀.excess Z lam+localHistoryCostScale a (E₀.countMoment y₀ (8*a))
        (localFieldEnvelope E₀ y₀ a ha Z lam)*(n:ℝ)*((n:ℝ)+3)^8)+
        localHistoryCostScale a (E₀.countMoment y₀ (8*a)) (localFieldEnvelope E₀ y₀ a ha Z lam)*((n:ℝ)+3)^8 := by linarith
      _ = _ := by ring

end CoulombAtom

end

end OAI
