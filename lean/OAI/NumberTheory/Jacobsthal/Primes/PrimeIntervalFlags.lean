import OAI.NumberTheory.Jacobsthal.Sieve.LargeModulusSiegelWalfisz

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset _root_.MeasureTheory
open scoped Topology
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma intervalPrimes_eq_sdiff {u v : ℝ} (hu : 0 ≤ u) (q : ℕ) (r : ℤ) :
    intervalPrimes u (v-u) q r = intervalPrimes 0 v q r \ intervalPrimes 0 u q r := by
  ext p
  simp only [mem_sdiff,mem_intervalPrimes,zero_add,add_sub_cancel]
  constructor
  · rintro ⟨hp,hlo,hhi,hm⟩
    refine ⟨⟨hp,by linarith,hhi,hm⟩,?_⟩
    rintro ⟨_,_,hpu,_⟩
    linarith
  · rintro ⟨⟨hp,h0,hhi,hm⟩,hnot⟩
    refine ⟨hp,?_,hhi,hm⟩
    by_contra h
    exact hnot ⟨hp,h0,le_of_not_gt h,hm⟩

lemma intervalPrimes_count_sub {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (q : ℕ) (r : ℤ) :
    ((intervalPrimes u (v-u) q r).card:ℝ) =
      ((intervalPrimes 0 v q r).card:ℝ)-((intervalPrimes 0 u q r).card:ℝ) := by
  have hs : intervalPrimes 0 u q r ⊆ intervalPrimes 0 v q r := by
    intro p hp
    obtain ⟨hpr,h0,hpu,hm⟩ := (mem_intervalPrimes _ _ _ _ _).mp hp
    exact (mem_intervalPrimes _ _ _ _ _).mpr ⟨hpr,h0,by linarith,hm⟩
  rw [intervalPrimes_eq_sdiff hu,card_sdiff_of_subset hs,Nat.cast_sub (card_le_card hs)]

lemma inv_log_intervalIntegrable {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (fun t:ℝ => 1/Real.log t) volume u v := by
  apply ContinuousOn.intervalIntegrable_of_Icc huv
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop)

lemma logarithmicIntegral_sub {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    logarithmicIntegral v-logarithmicIntegral u = ∫ t in u..v, 1/Real.log t := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (inv_log_intervalIntegrable (by norm_num) hu) (inv_log_intervalIntegrable hu huv)
  unfold logarithmicIntegral
  linarith

lemma logarithmicIntegral_sub_lower {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    (v-u)/Real.log v ≤ logarithmicIntegral v-logarithmicIntegral u := by
  have hv1 : 1 < v := by linarith
  rw [logarithmicIntegral_sub hu huv]
  calc
    _ = ∫ _t in u..v, 1/Real.log v := by simp; ring
    _ ≤ _ := intervalIntegral.integral_mono_on huv (by simp)
      (inv_log_intervalIntegrable hu huv) (fun t ht => by
        have ht1 : 1 < t := by linarith [ht.1]
        have hl : Real.log t ≤ Real.log v := Real.log_le_log (by linarith) ht.2
        exact one_div_le_one_div_of_le (Real.log_pos ht1) hl)

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

lemma ordinary_prime_count_exponential :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      |((intervalPrimes 0 X 1 0).card:ℝ)-logarithmicIntegral X| ≤
        C*X*Real.exp (-c*cubeHeight X) := by
  obtain ⟨c,C,X0,hc,hC,hX0,h⟩ := large_modulus_siegel_walfisz
  refine ⟨c,C,X0,hc,hC,hX0,?_⟩
  intro X hX
  have hx1 : 1 < X := by linarith
  have hq : (1:ℝ) ≤ Real.exp (c*cubeHeight X) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hc.le (cubeHeight_pos hx1).le)
  have he := h X hX 1 0 (by norm_num) (by norm_num) (by simpa only [Nat.cast_one,cubeHeight] using! hq)
  simpa only [Nat.totient_one,Nat.cast_one,div_one,cubeHeight] using! he

lemma prime_interval_lower_of_errors {c C u v : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hu : 2 ≤ u) (huv : u ≤ v)
    (heU : |((intervalPrimes 0 u 1 0).card:ℝ)-logarithmicIntegral u| ≤ C*u*Real.exp (-c*cubeHeight u))
    (heV : |((intervalPrimes 0 v 1 0).card:ℝ)-logarithmicIntegral v| ≤ C*v*Real.exp (-c*cubeHeight v)) :
    (v-u)/Real.log v-2*C*v*Real.exp (-c*cubeHeight u) ≤
      ((intervalPrimes u (v-u) 1 0).card:ℝ) := by
  have hu0 : 0 ≤ u := by linarith
  have hv0 : 0 ≤ v := hu0.trans huv
  have hh := cubeHeight_mono (by linarith : 1<u) huv
  have hdecay : Real.exp (-c*cubeHeight v) ≤ Real.exp (-c*cubeHeight u) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hV : C*v*Real.exp (-c*cubeHeight v) ≤ C*v*Real.exp (-c*cubeHeight u) :=
    mul_le_mul_of_nonneg_left hdecay (mul_nonneg hC hv0)
  have hU : C*u*Real.exp (-c*cubeHeight u) ≤ C*v*Real.exp (-c*cubeHeight u) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huv hC) (Real.exp_pos _).le
  have hUupper := (abs_le.mp heU).2
  have hVlower := (abs_le.mp heV).1
  have hli := logarithmicIntegral_sub_lower hu huv
  rw [intervalPrimes_count_sub hu0 huv]
  linarith

lemma exponential_log_cube_tendsto {K : ℝ} (hK : 0 < K) :
    Tendsto (fun w:ℝ => Real.exp (K*(Real.log w)^3)) atTop atTop :=
  Real.tendsto_exp_atTop.comp
    (Filter.Tendsto.const_mul_atTop hK ((tendsto_pow_atTop (by decide : (3:ℕ)≠0)).comp Real.tendsto_log_atTop))

lemma cubeHeight_lower_of_exp_cube {R w u : ℝ} (hR : 0 < R) (hw : 1 < w) (hu : 1 ≤ u)
    (hbound : Real.exp (R^3*(Real.log w)^3) ≤ u) :
    R*Real.log w ≤ cubeHeight u := by
  have hlogw : 0 < Real.log w := Real.log_pos hw
  have hlog : R^3*(Real.log w)^3 ≤ Real.log u := by
    have h := Real.log_le_log (Real.exp_pos _) hbound
    simpa only [Real.log_exp] using h
  apply (pow_le_pow_iff_left₀ (mul_nonneg hR.le hlogw.le)
    (Real.rpow_nonneg (Real.log_nonneg hu) _) (by decide : (3:ℕ)≠0)).mp
  change (R*Real.log w)^3 ≤ (cubeHeight u)^3
  rw [cubeHeight_pow_three hu,mul_pow]
  exact hlog

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma moving_prime_interval_error_budget {c C D R L eps w u v : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hR : 0 < R) (heps : 0 < eps)
    (hRate : c*R=D+3) (hw : 3 ≤ w) (hu : 2 ≤ u) (huv : u ≤ v)
    (hlo : Real.exp (R^3*(Real.log w)^3) ≤ u)
    (hhi : v ≤ Real.exp (L*(Real.log w)^3))
    (hlen : v/w^D ≤ v-u)
    (hpoly : 2*C*L*(Real.log w)^3 ≤ eps*w^3) :
    2*C*v*Real.exp (-c*cubeHeight u) ≤ eps*(v-u)/Real.log v := by
  have hw0 : 0 < w := by linarith
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := hu0.trans_le huv
  have hlogv : 0 < Real.log v := Real.log_pos (by linarith)
  have hh := cubeHeight_lower_of_exp_cube hR (by linarith) (by linarith) hlo
  have hrate : (D+3)*Real.log w ≤ c*cubeHeight u := by
    have he := mul_le_mul_of_nonneg_left hh hc.le
    rw [← mul_assoc,hRate] at he
    exact he
  have hlogupper : Real.log v ≤ L*(Real.log w)^3 := by
    have he := Real.log_le_log hv0 hhi
    simpa only [Real.log_exp] using he
  let W : ℝ := w^D
  let Z : ℝ := w^3
  let decay : ℝ := Real.exp (-c*cubeHeight u)
  have hW : 0 < W := Real.rpow_pos_of_pos hw0 _
  have hZ : 0 < Z := pow_pos hw0 _
  have hdecay : 0 < decay := Real.exp_pos _
  have hpower : W*Z = Real.exp ((D+3)*Real.log w) := by
    dsimp [W,Z]
    rw [← Real.rpow_natCast w 3,← Real.rpow_add hw0,Real.rpow_def_of_pos hw0]
    congr 1
    push_cast
    ring
  have hcancel : decay*W*Z ≤ 1 := by
    rw [mul_assoc,hpower]
    dsimp [decay]
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hlen' : v ≤ (v-u)*W := (div_le_iff₀ hW).mp hlen
  have hbound : ((2*C*v*decay)*Real.log v)*W ≤ (eps*(v-u))*W := by
    calc
      _ = (2*C*Real.log v)*(v*decay*W) := by ring
      _ ≤ (2*C*(L*(Real.log w)^3))*(v*decay*W) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogupper (by positivity)) (by positivity)
      _ = (2*C*L*(Real.log w)^3)*(v*decay*W) := by ring
      _ ≤ (eps*Z)*(v*decay*W) := mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ = (eps*v)*(decay*W*Z) := by ring
      _ ≤ eps*v := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hcancel (by positivity : 0≤eps*v)
      _ ≤ eps*((v-u)*W) := mul_le_mul_of_nonneg_left hlen' heps.le
      _ = _ := by ring
  apply (le_div_iff₀ hlogv).mpr
  exact le_of_mul_le_mul_right hbound hW

lemma eventually_interval_polynomial_budget {C L eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ 2*C*L*(Real.log w)^3 ≤ eps*w^3 := by
  filter_upwards [eventually_ge_atTop (3:ℝ),
    Real.tendsto_log_atTop.eventually
      (eventually_polynomial_le_exp (2*C*L/eps) 3 (by norm_num : (0:ℝ)<1))]
    with w hw hp
  have hw0 : 0 < w := by linarith
  have hfirst : 2*C*L*(Real.log w)^3 ≤ eps*w := by
    have he := mul_le_mul_of_nonneg_right hp.2 heps.le
    rw [one_mul,Real.exp_log hw0] at he
    calc
      _ = ((2*C*L/eps)*(Real.log w)^3)*eps := by field_simp
      _ ≤ w*eps := he
      _ = _ := mul_comm _ _
  have hw3 : w ≤ w^3 := by nlinarith [sq_nonneg (w-1)]
  exact ⟨hw,hfirst.trans (mul_le_mul_of_nonneg_left hw3 heps.le)⟩

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem moving_prime_interval_lower (D : ℝ) (hD : 0 < D) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℝ, 0 < L → ∀ eps : ℝ, 0 < eps →
      ∃ w₀ : ℝ, 3 ≤ w₀ ∧ ∀ w : ℝ, w₀ ≤ w → ∀ u v : ℝ, u ≤ v →
        Real.exp (K*(Real.log w)^3) ≤ u → v ≤ Real.exp (L*(Real.log w)^3) →
        v/w^D ≤ v-u →
        (1-eps)*(v-u)/Real.log v ≤ ((intervalPrimes u (v-u) 1 0).card:ℝ) := by
  obtain ⟨c,C,X0,hc,hC,hX0,hcount⟩ := ordinary_prime_count_exponential
  let R : ℝ := (D+3)/c
  let K : ℝ := R^3
  have hR : 0 < R := by dsimp [R]; positivity
  have hK : 0 < K := pow_pos hR _
  have hRate : c*R=D+3 := by dsimp [R]; field_simp
  refine ⟨K,hK,?_⟩
  intro L _hL eps heps
  have hev : ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ u v : ℝ, u ≤ v →
      Real.exp (K*(Real.log w)^3) ≤ u → v ≤ Real.exp (L*(Real.log w)^3) →
      v/w^D ≤ v-u →
      (1-eps)*(v-u)/Real.log v ≤ ((intervalPrimes u (v-u) 1 0).card:ℝ) := by
    filter_upwards [eventually_interval_polynomial_budget (C:=C) (L:=L) heps,
      (exponential_log_cube_tendsto hK).eventually (eventually_ge_atTop X0)]
      with w hpoly hlarge
    refine ⟨hpoly.1,?_⟩
    intro u v huv hlo hhi hlen
    have hXu : X0 ≤ u := hlarge.trans hlo
    have hXv : X0 ≤ v := hXu.trans huv
    have hu2 : 2 ≤ u := by linarith
    have herr := moving_prime_interval_error_budget hc hC.le hR heps hRate hpoly.1 hu2 huv hlo hhi hlen hpoly.2
    have hlower := prime_interval_lower_of_errors hc.le hC.le hu2 huv (hcount u hXu) (hcount v hXv)
    calc
      _ = (v-u)/Real.log v-eps*(v-u)/Real.log v := by ring
      _ ≤ (v-u)/Real.log v-2*C*v*Real.exp (-c*cubeHeight u) := sub_le_sub_left herr _
      _ ≤ _ := hlower
  obtain ⟨b,hb⟩ := eventually_atTop.mp hev
  refine ⟨max 3 b,le_max_left _ _,?_⟩
  intro w hw u v huv hlo hhi hlen
  exact (hb w ((le_max_right _ _).trans hw)).2 u v huv hlo hhi hlen

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset
open scoped Topology

noncomputable def primeIntervalFlags (includeLower includeUpper : Bool) (u v : ℝ) : Finset ℕ :=
  (range (⌊max v 0⌋₊+1)).filter (fun p:ℕ => p.Prime ∧
    (if includeLower then u ≤ (p:ℝ) else u < (p:ℝ)) ∧
    (if includeUpper then (p:ℝ) ≤ v else (p:ℝ) < v))

lemma mem_primeIntervalFlags (includeLower includeUpper : Bool) (u v : ℝ) (p : ℕ) :
    p ∈ primeIntervalFlags includeLower includeUpper u v ↔ p.Prime ∧
      (if includeLower then u ≤ (p:ℝ) else u < (p:ℝ)) ∧
      (if includeUpper then (p:ℝ) ≤ v else (p:ℝ) < v) := by
  constructor
  · intro hp
    exact (mem_filter.mp hp).2
  · intro hp
    have hv : (p:ℝ) ≤ v := by
      cases includeUpper
      · exact (show (p:ℝ)<v by simpa using hp.2.2).le
      · simpa using hp.2.2
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ?_),hp⟩
    exact (Nat.le_floor_iff (le_max_right v 0)).mpr (hv.trans (le_max_left _ _))

lemma primeIntervalFlags_lower_card (includeLower includeUpper : Bool) (u v : ℝ) :
    (intervalPrimes u (v-u) 1 0).card ≤ (primeIntervalFlags includeLower includeUpper u v).card+1 := by
  classical
  have hs : intervalPrimes u (v-u) 1 0 ⊆ primeIntervalFlags includeLower includeUpper u v ∪ {⌊v⌋₊} := by
    intro p hp
    obtain ⟨hpr,hlo,hhi,_⟩ := (mem_intervalPrimes _ _ _ _ _).mp hp
    have hpv : (p:ℝ) ≤ v := by linarith
    by_cases heq : (p:ℝ)=v
    · apply mem_union_right
      apply mem_singleton.mpr
      rw [← heq,Nat.floor_natCast]
    · apply mem_union_left
      apply (mem_primeIntervalFlags _ _ _ _ _).mpr
      refine ⟨hpr,?_,?_⟩
      · cases includeLower
        · simpa using hlo
        · simpa using hlo.le
      · have hvlt : (p:ℝ)<v := lt_of_le_of_ne hpv heq
        cases includeUpper
        · simpa using hvlt
        · simpa using hpv
  have hc := (card_le_card hs).trans (card_union_le _ _)
  simpa only [card_singleton] using hc

lemma primeIntervalFlags_upper_card (includeLower includeUpper : Bool) (u v : ℝ) :
    (primeIntervalFlags includeLower includeUpper u v).card ≤ (intervalPrimes u (v-u) 1 0).card+1 := by
  classical
  have hs : primeIntervalFlags includeLower includeUpper u v ⊆ intervalPrimes u (v-u) 1 0 ∪ {⌊u⌋₊} := by
    intro p hp
    obtain ⟨hpr,hlo,hhi⟩ := (mem_primeIntervalFlags _ _ _ _ _).mp hp
    by_cases heq : (p:ℝ)=u
    · apply mem_union_right
      apply mem_singleton.mpr
      rw [← heq,Nat.floor_natCast]
    · apply mem_union_left
      apply (mem_intervalPrimes _ _ _ _ _).mpr
      refine ⟨hpr,?_,?_,?_⟩
      · cases includeLower
        · simpa using hlo
        · have hu : u ≤ (p:ℝ) := by simpa using hlo
          exact lt_of_le_of_ne hu (fun he => heq he.symm)
      · have hv : (p:ℝ) ≤ v := by
          cases includeUpper
          · exact (show (p:ℝ)<v by simpa using hhi).le
          · simpa using hhi
        linarith
      · norm_num [Int.ModEq]
  have hc := (card_le_card hs).trans (card_union_le _ _)
  simpa only [card_singleton] using hc

lemma primeIntervalFlags_card_difference (includeLower includeUpper : Bool) (u v : ℝ) :
    |((primeIntervalFlags includeLower includeUpper u v).card:ℝ)-
      ((intervalPrimes u (v-u) 1 0).card:ℝ)| ≤ 1 := by
  have hlo : ((intervalPrimes u (v-u) 1 0).card:ℝ) ≤
      ((primeIntervalFlags includeLower includeUpper u v).card:ℝ)+1 := by
    exact_mod_cast primeIntervalFlags_lower_card includeLower includeUpper u v
  have hhi : ((primeIntervalFlags includeLower includeUpper u v).card:ℝ) ≤
      ((intervalPrimes u (v-u) 1 0).card:ℝ)+1 := by
    exact_mod_cast primeIntervalFlags_upper_card includeLower includeUpper u v
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem moving_prime_interval_lower_flags (D : ℝ) (hD : 0 < D) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℝ, 0 < L → ∀ eps : ℝ, 0 < eps →
      ∃ w₀ : ℝ, 3 ≤ w₀ ∧ ∀ w : ℝ, w₀ ≤ w → ∀ u v : ℝ, u ≤ v →
        Real.exp (K*(Real.log w)^3) ≤ u → v ≤ Real.exp (L*(Real.log w)^3) →
        v/w^D ≤ v-u → ∀ includeLower includeUpper : Bool,
        (1-eps)*(v-u)/Real.log v-1 ≤ ((primeIntervalFlags includeLower includeUpper u v).card:ℝ) := by
  obtain ⟨K,hK,h⟩ := moving_prime_interval_lower D hD
  refine ⟨K,hK,?_⟩
  intro L hL eps heps
  obtain ⟨w0,hw0,hw⟩ := h L hL eps heps
  refine ⟨w0,hw0,?_⟩
  intro w hww u v huv hlo hhi hlen includeLower includeUpper
  have he := hw w hww u v huv hlo hhi hlen
  have hc : ((intervalPrimes u (v-u) 1 0).card:ℝ) ≤
      ((primeIntervalFlags includeLower includeUpper u v).card:ℝ)+1 := by
    exact_mod_cast primeIntervalFlags_lower_card includeLower includeUpper u v
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
