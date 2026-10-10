import OAI.Probability.DirectionalWalk.DyadicCover

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma axisCube_log_bound {d : ℕ} (e : Step d) (J : ℕ) (hJ : 0 < J) :
    Real.log (Fintype.card (AxisCubeSite e (2^J) ((2^J)^2+1))+1) ≤
      (d+1)*6*J := by
  have hc := card_axisCubeSite_le e (2^J) ((2^J)^2+1)
  have hpow : (2:ℕ)^(2*J) = ((2:ℕ)^J)^2 := by rw [Nat.mul_comm 2 J,pow_mul]
  have hb : 2*((2:ℕ)^J)^2+3 ≤ 2^(2*J+3) := by
    rw [pow_add,hpow]
    have hh : 1 ≤ ((2:ℕ)^J)^2 := one_le_pow₀ (one_le_pow₀ (by norm_num))
    norm_num at *
    omega
  have hbase : 2*((2:ℕ)^J)^2+3 = 2*(((2:ℕ)^J)^2+1)+1 := by ring
  rw [hbase] at hb
  have hp : (2*(((2:ℕ)^J)^2+1)+1)^d ≤ 2^((2*J+3)*d) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hb d
  have hc' : Fintype.card (AxisCubeSite e (2^J) ((2^J)^2+1))+1 ≤ 2^((2*J+3)*d+1) := by
    have hh := hc.trans hp
    have h1 : 1 ≤ (2:ℕ)^((2*J+3)*d) := one_le_pow₀ (by norm_num)
    rw [pow_succ (2:ℕ) ((2*J+3)*d)]
    omega
  have hh := Real.log_le_log (by positivity : 0 < (Fintype.card (AxisCubeSite e (2^J) ((2^J)^2+1)) : ℝ)+1)
    (show (Fintype.card (AxisCubeSite e (2^J) ((2^J)^2+1)) : ℝ)+1 ≤ (2:ℝ)^((2*J+3)*d+1) by exact_mod_cast hc')
  rw [Real.log_pow] at hh
  have hl : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hm : 0 ≤ (((2*J+3)*d+1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hv := mul_le_mul_of_nonneg_left hl hm
  push_cast at hh hv
  have hj : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith

lemma summable_shifted_axisTail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) :
    Summable (fun l => (2:ℝ)^l*(axisWidthTail μ e (2^(l-1))).toReal) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.add_sub_cancel,pow_succ,mul_assoc,mul_comm,mul_left_comm] using
    (summable_dyadic_axisWidthTail μ hell e hp).mul_left 2

lemma axis_delta_dyadic {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e)))
    (l G : ℕ) (hG : 1 ≤ G) (hGl : G ≤ l) :
    axisReachProb μ e (2^l-2^(l-G))-axisReachProb μ e (2^l) ≤
      ENNReal.ofReal ((1/2 : ℝ)^G*((2:ℝ)^l*(axisWidthTail μ e (2^(l-1))).toReal)) := by
  let := slabLaw_probability μ (axisDirection e) hp
  have hlow : (2:ℕ)^(l-G) ≤ 2^l := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have hhalf : (2:ℕ)^(l-1) ≤ 2^l-2^(l-G) := by
    have hh : (2:ℕ)^(l-G) ≤ 2^(l-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow : (2:ℕ)^l = 2^(l-1)*2 := by
      conv_lhs => rw [show l = (l-1)+1 by omega,pow_succ]
    omega
  have hr := (axis_renewal_tail_bound μ hell e hp (Nat.sub_le ((2:ℕ)^l) ((2:ℕ)^(l-G)))).2
  have ht := ENNReal.toReal_mono (measure_ne_top _ _) (axisWidthTail_antitone μ e hhalf)
  change (axisWidthTail μ e (2^l-2^(l-G))).toReal ≤ (axisWidthTail μ e (2^(l-1))).toReal at ht
  have hpow : (2:ℝ)^(l-G) = (1/2 : ℝ)^G*(2:ℝ)^l := by
    have he : l = (l-G)+G := by omega
    rw [show (2:ℝ)^l = (2:ℝ)^(l-G)*(2:ℝ)^G from by rw [← pow_add, ← he]]
    rw [div_pow,one_pow]
    field_simp
  have hreal : (axisReachProb μ e (2^l-2^(l-G))).toReal-(axisReachProb μ e (2^l)).toReal ≤
      (1/2 : ℝ)^G*((2:ℝ)^l*(axisWidthTail μ e (2^(l-1))).toReal) := by
    have hrr : ((2^l : ℕ) : ℝ)-((2^l-2^(l-G) : ℕ) : ℝ) = (2:ℝ)^(l-G) := by
      rw [Nat.cast_sub hlow];push_cast;ring
    rw [hrr] at hr
    exact hr.trans (by simpa only [hpow,mul_assoc] using mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ)≤(2:ℝ)^(l-G)))
  apply (ENNReal.toReal_le_toReal (lt_of_le_of_lt tsub_le_self (measure_lt_top _ _)).ne ENNReal.ofReal_ne_top).mp
  change (axisReachProb μ e (2^l-2^(l-G))-axisReachProb μ e (2^l)).toReal ≤ (ENNReal.ofReal _).toReal
  rw [ENNReal.toReal_sub_of_le (axisReachProb_antitone μ e (Nat.sub_le _ _)) (measure_ne_top _ _),
    ENNReal.toReal_ofReal (by positivity)]
  exact hreal

lemma dyadic_markov_ratio (l G c : ℕ) (h : G+c ≤ l) (W : ℝ) :
    ((4*2^(l-G-c) : ℕ) : ℝ)*W/((2^(l-G) : ℕ) : ℝ) = 4*W*(1/2 : ℝ)^c := by
  have he : l-G = (l-G-c)+c := by omega
  push_cast
  rw [show (2:ℝ)^(l-G) = (2:ℝ)^(l-G-c)*(2:ℝ)^c from by rw [← pow_add, ← he]]
  rw [div_pow,one_pow]
  field_simp

lemma commonBand_good_label {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b))))
    (J G c l m : ℕ) (hG : 0 < G) (hl : G+c ≤ l) (hlJ : l < J)
    (hΔ : (1/2 : ℝ)^G*((2:ℝ)^l*(axisWidthTail μ e (2^(l-1))).toReal) ≤ (1/2 : ℝ)^m) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
    (annealed μ 0).real (nonBacktracking (axisDirection e))^2 ≤
      4*(∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν)*(1/2 : ℝ)^c +
      (∑ j ∈ Finset.Icc (l-(G+c)) l, (twoTapeLaw ν).real (commonBandContact e (2^j))) +
      (∫ a, slabRadius a ∂ν false)*(1/2 : ℝ)^J +
      ((annealed μ 0).real (nonBacktracking (axisDirection e)))⁻¹ *
      ((annealed μ 0).real (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ((24 / posteriorExponent)*((d+1)*6*J)*(m+1)^2*(1/2 : ℝ)^m) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) := fun b => slabLaw_probability μ _ (hp b)
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  have hlpos : 0 < (2:ℕ)^l := by positivity
  have hh := commonBand_lower_real μ hell e hp (2^l) (2^J) (2^(l-G)) (2^(l+1)) m
    (l-G-c) l (by positivity) (Nat.pow_le_pow_right (by norm_num) hlJ.le)
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)) (by rw [pow_succ];omega)
    (by omega) (by positivity) (by rw [pow_succ];omega)
    ((axis_delta_dyadic μ hell e (hp false) l G hG (by omega)).trans (ENNReal.ofReal_le_ofReal hΔ))
  dsimp only at hh
  rw [dyadic_markov_ratio l G c hl,show l-G-c = l-(G+c) by omega] at hh
  have hrad : (∫ a, slabRadius a ∂ν false)/((2^J : ℕ) : ℝ) =
      (∫ a, slabRadius a ∂ν false)*(1/2 : ℝ)^J := by push_cast;rw [div_pow,one_pow];ring
  rw [hrad] at hh
  have hlog := axisCube_log_bound e J (by omega)
  have hc : 0 ≤ ((annealed μ 0).real (nonBacktracking (axisDirection e)))⁻¹ *
      ((annealed μ 0).real (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ := by positivity
  have hm : 0 ≤ (24/posteriorExponent)*(m+1)^2*(1/2 : ℝ)^m := by have := posteriorExponent_pos;positivity
  have hb := mul_le_mul_of_nonneg_left hlog (mul_nonneg hc hm)
  nlinarith

lemma sum_trailing_windows (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (J w : ℕ) :
    (∑ l ∈ Finset.range J, ∑ j ∈ Finset.Icc (l-w) l, p j) ≤
      (w+1)*∑ j ∈ Finset.range J, p j := by
  classical
  have hid (l : ℕ) (hl : l ∈ Finset.range J) :
      (∑ j ∈ Finset.Icc (l-w) l, p j) =
        ∑ j ∈ Finset.range J, if j ≤ l ∧ l ≤ j+w then p j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
    have hl' := Finset.mem_range.mp hl
    omega
  rw [Finset.sum_congr rfl hid,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [← Finset.sum_filter,Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.range J).filter (fun l => j ≤ l ∧ l ≤ j+w)).card ≤ w+1 := by
    have hs : (Finset.range J).filter (fun l => j ≤ l ∧ l ≤ j+w) ⊆ Finset.Icc j (j+w) := by
      intro l hl
      exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hl).2
    have hh := Finset.card_le_card hs
    simp only [Nat.card_Icc] at hh
    omega
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hp j)

lemma sum_early_labels (J w : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (∑ l ∈ Finset.range J, if l < w then c else 0) ≤ w*c := by
  classical
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have hs : ((Finset.range J).filter (fun l => l < w)) ⊆ Finset.range w := by
    intro l hl
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hl).2
  have hh := Finset.card_le_card hs
  simp only [Finset.card_range] at hh
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hh) hc

lemma window_count_lower (p a : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (ha : ∀ j, 0 ≤ a j)
    (S C c : ℝ) (hS : ∀ J, ∑ l ∈ Finset.range J, a l ≤ S)
    (hC : 0 < C) (hc : 0 < c) (hSC : 4*S ≤ C)
    (J w : ℕ) (hwJ : 4*w ≤ J)
    (hgood : ∀ l, w ≤ l → l < J → a l ≤ C/J → c ≤ ∑ j ∈ Finset.Icc (l-w) l, p j) :
    c*J/2 ≤ (w+1)*∑ j ∈ Finset.range J, p j := by
  classical
  by_cases hJ : J = 0
  · subst J
    simp
  have hJ0 : (0:ℝ) < J := by exact_mod_cast Nat.pos_of_ne_zero hJ
  have hpoint (l : ℕ) (hl : l ∈ Finset.range J) :
      c ≤ (if l < w then c else 0)+(∑ j ∈ Finset.Icc (l-w) l, p j)+(c*J/C)*a l := by
    have hs : 0 ≤ ∑ j ∈ Finset.Icc (l-w) l, p j := Finset.sum_nonneg (fun j _ => hp j)
    have he : 0 ≤ (c*J/C)*a l := mul_nonneg (by positivity) (ha l)
    by_cases hlw : l < w
    · simp only [hlw,↓reduceIte]
      linarith
    simp only [hlw,↓reduceIte,zero_add]
    by_cases hg : a l ≤ C/J
    · linarith [hgood l (by omega) (Finset.mem_range.mp hl) hg]
    · have hh : C/J ≤ a l := le_of_not_ge hg
      have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ c*J/C)
      have hid : (c*J/C)*(C/J) = c := by field_simp
      rw [hid] at hm
      linarith
  have hh := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    ← Finset.mul_sum] at hh
  have hearly := sum_early_labels J w c hc.le
  have hwindows := sum_trailing_windows p hp J w
  have htail := mul_le_mul_of_nonneg_left (hS J) (by positivity : 0 ≤ c*J/C)
  have htail' : (c*J/C)*S ≤ c*J/4 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have hh := mul_le_mul_of_nonneg_left hSC (by positivity : 0 ≤ c*J/C)
    have hid : (c*J/C)*C = c*J := by field_simp
    rw [hid] at hh
    nlinarith
  have hearly' : w*c ≤ c*J/4 := by
    have hw : (4:ℝ)*w ≤ J := by exact_mod_cast hwJ
    nlinarith
  linarith

lemma tendsto_dyadic_quadratic :
    Tendsto (fun t : ℕ => ((t:ℝ)+1)^2*(1/2 : ℝ)^t) atTop (𝓝 0) := by
  have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have hh := (h2.add (h1.const_mul 2)).add h0
  convert hh using 1 <;> simp only [pow_zero,pow_one,mul_zero,add_zero]
  ext t
  ring

lemma eventually_dyadic_quadratic_lt (D ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, D*(((t:ℝ)+1)^2*(1/2 : ℝ)^t) < ε := by
  have hh := tendsto_dyadic_quadratic.const_mul D
  simp only [mul_zero] at hh
  exact hh.eventually (gt_mem_nhds hε)

lemma dyadic_decay_le_quadratic (t : ℕ) :
    (1/2 : ℝ)^t ≤ ((t:ℝ)+1)^2*(1/2 : ℝ)^t := by
  have ht : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have hp : (0:ℝ) ≤ (1/2:ℝ)^t := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ ((t:ℝ)+1)^2 by nlinarith) hp]

lemma self_dyadic_decay_le_quadratic (t : ℕ) :
    t*(1/2 : ℝ)^t ≤ ((t:ℝ)+1)^2*(1/2 : ℝ)^t := by
  have ht : (0:ℝ) ≤ t := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right (by nlinarith : (t:ℝ) ≤ ((t:ℝ)+1)^2) (by positivity)

lemma dyadic_decay_antitone : Antitone (fun t : ℕ => (1/2 : ℝ)^t) := by
  intro a b hab
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hab

lemma dyadic_power_cancel (a b : ℕ) :
    (2:ℝ)^a*(1/2 : ℝ)^(a+b) = (1/2 : ℝ)^b := by
  simp only [pow_add,div_pow,one_pow]
  field_simp

lemma dyadic_delta_identity (a t : ℕ) :
    (1/2 : ℝ)^(2*t)*((2:ℝ)^t/(2:ℝ)^a) = (1/2 : ℝ)^(a+t) := by
  simp only [show 2*t=t+t by omega,pow_add,div_pow,one_pow]
  field_simp

lemma dyadic_large_parameters (K c : ℕ) (hK : 0 < K)
    (C R E B P : ℝ) (hC : 0 < C) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hB : 0 ≤ B) (hP : 0 < P) :
    ∃ t : ℕ, c+1 ≤ t ∧ 0 < t ∧
      C ≤ (2:ℝ)^t ∧
      4*(2*t+c) ≤ (2:ℕ)^(2*K*t) ∧
      R*(1/2 : ℝ)^((2:ℕ)^(2*K*t)) ≤ P/8 ∧
      E*((2:ℕ)^(2*K*t) : ℝ)*(((2*K+1)*t : ℕ)+1 : ℝ)^2*(1/2 : ℝ)^((2*K+1)*t) ≤ P/8 ∧
      ((K*t : ℕ):ℝ)*Real.log 2*(2:ℝ)^(K*t)*B ≤ ((2:ℕ)^(2*K*t) : ℝ) := by
  have hP8 : (0:ℝ) < P/8 := by positivity
  obtain ⟨t,ht,htC,htwin,htR,htE,htB⟩ := ((eventually_ge_atTop (c+1)).and
    ((eventually_dyadic_quadratic_lt C 1 (by norm_num)).and
    ((eventually_dyadic_quadratic_lt (8+4*c) 1 (by norm_num)).and
    ((eventually_dyadic_quadratic_lt R (P/8) hP8).and
    ((eventually_dyadic_quadratic_lt (E*(2*K+2)^2) (P/8) hP8).and
    (eventually_dyadic_quadratic_lt (K*Real.log 2*B) 1 (by norm_num))))))).exists
  have htpos : 0 < t := by omega
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg _
  have htKt : t ≤ K*t := by nlinarith only [hK]
  have ht2Kt : t ≤ 2*K*t := by nlinarith only [htKt]
  have hpow : (2:ℕ)^t ≤ 2^(2*K*t) := Nat.pow_le_pow_right (by norm_num) ht2Kt
  have htJ : t ≤ (2:ℕ)^(2*K*t) := (Nat.lt_two_pow_self (n := t)).le.trans hpow
  have hCpow : C ≤ (2:ℝ)^t := by
    have hh := (mul_le_mul_of_nonneg_left (dyadic_decay_le_quadratic t) hC.le).trans htC.le
    simpa only [div_pow,one_pow,← div_eq_mul_one_div,div_le_one (by positivity : (0:ℝ)<(2:ℝ)^t)] using hh
  have hw : 4*(2*t+c) ≤ (2:ℕ)^t := by
    have hpol : (4:ℝ)*(2*t+c) ≤ (8+4*c)*((t:ℝ)+1)^2 := by
      have hx : (0:ℝ) ≤ (8+4*c)*(t:ℝ)^2+(8+8*c)*t+8 := by positivity
      nlinarith only [hx]
    have hh := (mul_le_mul_of_nonneg_right hpol (by positivity : (0:ℝ)≤(1/2:ℝ)^t)).trans (by nlinarith only [htwin] : (8+4*c)*((t:ℝ)+1)^2*(1/2:ℝ)^t ≤ 1)
    have hh' : (4:ℝ)*(2*t+c) ≤ (2:ℝ)^t := by
      simpa only [div_pow,one_pow,← div_eq_mul_one_div,div_le_one (by positivity : (0:ℝ)<(2:ℝ)^t)] using hh
    exact_mod_cast hh'
  have hr : R*(1/2 : ℝ)^((2:ℕ)^(2*K*t)) ≤ P/8 :=
    (mul_le_mul_of_nonneg_left ((dyadic_decay_antitone htJ).trans (dyadic_decay_le_quadratic t)) hR).trans htR.le
  have hm : ((2*K+1)*t : ℕ) = 2*K*t+t := by ring
  have hrealM : ((((2*K+1)*t : ℕ):ℝ)+1)^2 ≤ (2*K+2)^2*((t:ℝ)+1)^2 := by
    have hcmp : (((2*K+1)*t : ℕ):ℝ)+1 ≤ (2*K+2)*((t:ℝ)+1) := by
      push_cast
      nlinarith only [hK0,ht0]
    simpa only [mul_pow] using (sq_le_sq₀ (by positivity) (by positivity)).mpr hcmp
  have herror : E*((2:ℕ)^(2*K*t) : ℝ)*(((2*K+1)*t : ℕ)+1 : ℝ)^2*(1/2 : ℝ)^((2*K+1)*t) ≤ P/8 := by
    have hi : (2:ℝ)^(2*K*t)*(1/2 : ℝ)^((2*K+1)*t) = (1/2 : ℝ)^t := by
      rw [hm]
      exact dyadic_power_cancel (2*K*t) t
    have heq : E*((2:ℕ)^(2*K*t) : ℝ)*(((2*K+1)*t : ℕ)+1 : ℝ)^2*(1/2 : ℝ)^((2*K+1)*t) =
        E*((((2*K+1)*t : ℕ):ℝ)+1)^2*(1/2 : ℝ)^t := by
      calc
        _ = (E*((((2*K+1)*t : ℕ):ℝ)+1)^2)*((2:ℝ)^(2*K*t)*(1/2 : ℝ)^((2*K+1)*t)) := by push_cast;ring
        _ = _ := by rw [hi]
    rw [heq]
    have hm' := mul_le_mul_of_nonneg_left hrealM (mul_nonneg hE (by positivity : (0:ℝ)≤(1/2:ℝ)^t))
    have he' : E*(↑((2*K+1)*t)+1)^2*(1/2:ℝ)^t ≤ E*(2*K+2)^2*(((t:ℝ)+1)^2*(1/2:ℝ)^t) := by
      nlinarith only [hm']
    exact he'.trans htE.le
  have hcor : ((K*t : ℕ):ℝ)*Real.log 2*(2:ℝ)^(K*t)*B ≤ ((2:ℕ)^(2*K*t) : ℝ) := by
    have hcoef : 0 ≤ (K:ℝ)*Real.log 2*B := by positivity
    have hh := (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (dyadic_decay_antitone htKt) ht0 |>.trans (self_dyadic_decay_le_quadratic t)) hcoef).trans htB.le
    have hp2 : (2:ℝ)^(2*K*t) = (2:ℝ)^(K*t)*(2:ℝ)^(K*t) := by rw [← pow_add];congr 1;ring
    push_cast
    rw [hp2]
    have hh' : (K:ℝ)*Real.log 2*B*t ≤ (2:ℝ)^(K*t) := by
      have hx : ((K:ℝ)*Real.log 2*B*t)*(1/2:ℝ)^(K*t) ≤ 1 := by nlinarith only [hh]
      simpa only [div_pow,one_pow,← div_eq_mul_one_div,div_le_one (by positivity : (0:ℝ)<(2:ℝ)^(K*t))] using hx
    nlinarith only [mul_le_mul_of_nonneg_right hh' (by positivity : (0:ℝ)≤(2:ℝ)^(K*t))]
  exact ⟨t,ht,htpos,hCpow,hw.trans hpow,hr,herror,hcor⟩

end DirectionalZeroOne

end OAI
