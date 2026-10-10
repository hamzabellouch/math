import OAI.Probability.DirectionalWalk.EntropyUpperBound

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma dyadic_entropy_contradiction (p a : ℕ → ℝ)
    (hp : ∀ j, 0 ≤ p j) (ha : ∀ j, 0 ≤ a j) (hs : Summable a)
    (P W R E A B : ℝ) (hP : 0 < P) (hW : 0 ≤ W) (hR : 0 ≤ R)
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlower : ∀ (J G c l m : ℕ), 0 < G → G+c ≤ l → l < J →
      (1/2 : ℝ)^G*a l ≤ (1/2 : ℝ)^m →
      P ≤ W*(1/2 : ℝ)^c + (∑ j ∈ Finset.Icc (l-(G+c)) l, p j) +
        R*(1/2 : ℝ)^J + E*J*(m+1)^2*(1/2 : ℝ)^m)
    (hupper : ∀ J L : ℕ, (L*Real.log 2)*(∑ j ∈ Finset.range J, p j) ≤
      A*J+(L*Real.log 2)*(2:ℝ)^L*B) : False := by
  let S := ∑' j, a j
  let C := 4*S+1
  have hS0 : 0 ≤ S := tsum_nonneg ha
  have hC : 0 < C := by dsimp [C];linarith
  have hSC : 4*S ≤ C := by dsimp [C];linarith
  have hS (J : ℕ) : ∑ j ∈ Finset.range J, a j ≤ S :=
    Summable.sum_le_tsum _ (fun j _ => ha j) hs
  obtain ⟨c,hc⟩ := (eventually_dyadic_quadratic_lt W (P/4) (by positivity)).exists
  have hcsmall : W*(1/2 : ℝ)^c < P/4 :=
    (mul_le_mul_of_nonneg_left (dyadic_decay_le_quadratic c) hW).trans_lt hc
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨K,hK⟩ := exists_nat_gt (12*(A+1)/(P*Real.log 2))
  have hk0 : (0:ℝ) ≤ 12*(A+1)/(P*Real.log 2) := by positivity
  have hKpos : 0 < K := by exact_mod_cast (lt_of_le_of_lt hk0 hK)
  have hKbig : 3*(A+1) < P*K*Real.log 2/4 := by
    have hh := (div_lt_iff₀ (mul_pos hP hlog)).mp hK
    nlinarith only [hh]
  obtain ⟨t,htc,ht,hCt,hwJ,hr,herr,hcorr⟩ :=
    dyadic_large_parameters K c hKpos C R E B P hC hR hE hB hP
  let J := (2:ℕ)^(2*K*t)
  let w := 2*t+c
  have hJpos : (0:ℝ) < J := by dsimp [J];positivity
  have htpos : (0:ℝ) < t := by exact_mod_cast ht
  have hw : (w:ℝ)+1 ≤ 3*t := by
    have hh : (c:ℝ)+1 ≤ t := by exact_mod_cast htc
    dsimp [w]
    push_cast
    linarith only [hh]
  have hlabel (l : ℕ) (hwl : w ≤ l) (hlJ : l < J) (hgood : a l ≤ C/J) :
      P/2 ≤ ∑ j ∈ Finset.Icc (l-w) l, p j := by
    have hdelta : (1/2 : ℝ)^(2*t)*a l ≤ (1/2 : ℝ)^((2*K+1)*t) := by
      calc
        _ ≤ (1/2 : ℝ)^(2*t)*(C/J) := mul_le_mul_of_nonneg_left hgood (by positivity)
        _ ≤ (1/2 : ℝ)^(2*t)*((2:ℝ)^t/J) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hCt hJpos.le) (by positivity)
        _ = _ := by
          dsimp [J]
          push_cast
          rw [dyadic_delta_identity]
          congr 1
          ring
    have hh := hlower J (2*t) c l ((2*K+1)*t) (by omega) hwl hlJ hdelta
    change P ≤ W*(1/2:ℝ)^c + (∑ j ∈ Finset.Icc (l-w) l, p j) + R*(1/2:ℝ)^J +
      E*J*((((2*K+1)*t : ℕ):ℝ)+1)^2*(1/2:ℝ)^((2*K+1)*t) at hh
    change R*(1/2:ℝ)^J ≤ P/8 at hr
    have herr' : E*J*((((2*K+1)*t : ℕ):ℝ)+1)^2*(1/2:ℝ)^((2*K+1)*t) ≤ P/8 := by
      simpa only [J,Nat.cast_pow,Nat.cast_ofNat] using herr
    linarith only [hh,hcsmall,hr,herr']
  have hc2 : 0 < P/2 := by positivity
  have hcount := window_count_lower p a hp ha S C (P/2) hS hC hc2 hSC J w hwJ hlabel
  have hu := hupper J (K*t)
  have hu' : (((K*t : ℕ):ℝ)*Real.log 2)*(∑ j ∈ Finset.range J,p j) ≤ (A+1)*J := by
    have hcorr' : ((K*t : ℕ):ℝ)*Real.log 2*(2:ℝ)^(K*t)*B ≤ (J:ℝ) := by
      simpa only [J,Nat.cast_pow,Nat.cast_ofNat] using hcorr
    linarith only [hu,hcorr']
  have hcoef : 0 ≤ ((K*t : ℕ):ℝ)*Real.log 2 := by positivity
  have hAJ : 0 ≤ (A+1)*(J:ℝ) := by positivity
  have hfinal : (P*K*Real.log 2/4)*(t:ℝ)*(J:ℝ) ≤ (3*(A+1))*(t:ℝ)*(J:ℝ) := by
    calc
      _ = (((K*t : ℕ):ℝ)*Real.log 2)*((P/2)*J/2) := by push_cast;ring
      _ ≤ (((K*t : ℕ):ℝ)*Real.log 2)*((w+1)*(∑ j ∈ Finset.range J,p j)) :=
        mul_le_mul_of_nonneg_left hcount hcoef
      _ = (w+1)*((((K*t : ℕ):ℝ)*Real.log 2)*(∑ j ∈ Finset.range J,p j)) := by ring
      _ ≤ (w+1)*((A+1)*J) := mul_le_mul_of_nonneg_left hu' (by positivity)
      _ ≤ (3*t)*((A+1)*J) := mul_le_mul_of_nonneg_right hw hAJ
      _ = _ := by ring
  have hf := le_of_mul_le_mul_right (le_of_mul_le_mul_right hfinal hJpos) htpos
  exact not_le_of_gt hKbig hf

lemma not_both_axis_nonBacktracking {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b)))) : False := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
    fun b => slabLaw_probability μ _ (hp b)
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  let p (j : ℕ) := (twoTapeLaw ν).real (commonBandContact e (2^j))
  let a (l : ℕ) := (2:ℝ)^l*(axisWidthTail μ e (2^(l-1))).toReal
  let P := (annealed μ 0).real (nonBacktracking (axisDirection e))^2
  let W := 4*(∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν)
  let R := ∫ a, slabRadius a ∂ν false
  let E := ((annealed μ 0).real (nonBacktracking (axisDirection e)))⁻¹ *
      ((annealed μ 0).real (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
      (24/posteriorExponent)*((d+1)*6)
  have hpos : 0 < (annealed μ 0).real (nonBacktracking (axisDirection e)) :=
    ENNReal.toReal_pos (ne_of_gt (hp false)) (measure_ne_top _ _)
  have hP : 0 < P := by dsimp [P];positivity
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (integral_nonneg (fun _ => Nat.cast_nonneg _))
  have hR : 0 ≤ R := integral_nonneg slabRadius_nonneg
  have hE : 0 ≤ E := by dsimp [E];have := posteriorExponent_pos;positivity
  obtain ⟨A,B,hA,hB,hupper⟩ := commonBand_entropy_upper μ hell e hp
  apply dyadic_entropy_contradiction p a (fun _ => measureReal_nonneg)
    (fun _ => mul_nonneg (by positivity) ENNReal.toReal_nonneg)
    (summable_shifted_axisTail μ hell e (hp false)) P W R E A B hP hW hR hE hA hB _ hupper
  intro J G c l m hG hl hlJ hΔ
  have hh := commonBand_good_label μ hell e hp J G c l m hG hl hlJ hΔ
  dsimp only at hh
  dsimp only [P,W,R,E,p,ν]
  nlinarith only [hh]

theorem directional_zero_one (d : ℕ) (hd : 3 ≤ d)
    (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (ℓ : Fin d → ℝ) (hℓ : ℓ ≠ 0) :
    annealed μ 0 (escape ℓ) = 0 ∨ annealed μ 0 (escape ℓ) = 1 := by
  cases d with
  | zero => omega
  | succ d =>
    by_contra hh
    have hne0 : annealed μ 0 (escape ℓ) ≠ 0 := fun h => hh (Or.inl h)
    have hne1 : annealed μ 0 (escape ℓ) ≠ 1 := fun h => hh (Or.inr h)
    have h0 : 0 < annealed μ 0 (escape ℓ) := bot_lt_iff_ne_bot.mpr hne0
    have h1 : annealed μ 0 (escape ℓ) < 1 := lt_of_le_of_ne (prob_le_one) hne1
    obtain ⟨i,hi,hi'⟩ := mixed_direction_has_mixed_coordinate μ hell ℓ hℓ h0 h1
    apply not_both_axis_nonBacktracking μ hell (i,true)
    intro b
    cases b
    · simpa only [placedAxis, Bool.false_eq_true,↓reduceIte,axisDirection] using
        positive_nonBacktracking μ (Pi.single i 1) hi
    · change 0 < annealed μ 0 (nonBacktracking (axisDirection (oppositeStep (i,true))))
      rw [axisDirection_opposite]
      simpa only [axisDirection,↓reduceIte] using positive_nonBacktracking μ (-Pi.single i 1) hi'

end DirectionalZeroOne

end OAI
