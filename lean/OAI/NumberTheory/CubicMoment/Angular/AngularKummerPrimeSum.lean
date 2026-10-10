import OAI.NumberTheory.CubicMoment.Estimates.PublishedAngularKummerPrime
import OAI.NumberTheory.CubicMoment.Estimates.QuantitativeNoncube

namespace OAI

/-! The raw angular Chebyshev estimate implies the ordinary prime
Siegel--Walfisz bound. A square-root initial segment is bounded directly;
partial summation on the remaining interval has bounded reciprocal-log
variation. -/
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma reciprocal_log_variation {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    (∀ t ∈ Icc a b, DifferentiableAt ℝ (fun t => (1:ℂ)/(Real.log t:ℂ)) t) ∧
    IntegrableOn (deriv (fun t => (1:ℂ)/(Real.log t:ℂ))) (Icc a b) ∧
    ‖(1:ℂ)/(Real.log a:ℂ)‖+‖(1:ℂ)/(Real.log b:ℂ)‖+
      (∫ t in Ioc a b, ‖deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t‖) ≤ 3 := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le ha
  have hla : 1 ≤ Real.log a := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ha
  let f : ℝ → ℝ := fun t => 1/Real.log t
  let g : ℝ → ℝ := fun t => -(t⁻¹)/(Real.log t)^2
  have hder (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt f (g t) t := by
    convert! (hasDerivAt_const t (1:ℝ)).div
      (Real.hasDerivAt_log (ne_of_gt (zero_lt_one.trans (ha1.trans_le ht.1))))
      (Real.log_pos (ha1.trans_le ht.1)).ne' using 1
    simp only [g,zero_mul,one_mul,zero_sub]
  have hg : ContinuousOn g (Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans (ha1.trans_le ht.1))
    have hlt : Real.log t ≠ 0 := (Real.log_pos (ha1.trans_le ht.1)).ne'
    exact ((continuousAt_id.inv₀ ht0).neg.div ((Real.continuousAt_log ht0).pow 2)
      (pow_ne_zero 2 hlt)).continuousWithinAt
  have he (t : ℝ) (ht : t ∈ Icc a b) :
      deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t = (g t:ℂ) := by
    convert (hder t ht).ofReal_comp.deriv using 1
    simp only [f,Complex.ofReal_div,Complex.ofReal_one]
  have hi : IntegrableOn (deriv (fun t => (1:ℂ)/(Real.log t:ℂ))) (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hg).integrableOn_Icc.congr_fun
      (fun t ht => (he t ht).symm) measurableSet_Icc
  have hint : (∫ t in Ioc a b, ‖deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t‖) =
      f a-f b := by
    have hn (t : ℝ) (ht : t ∈ Icc a b) :
        ‖deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t‖ = -g t := by
      rw [he t ht,Complex.norm_real,Real.norm_of_nonpos]
      change -t⁻¹/(Real.log t)^2 ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr
        (zero_lt_one.trans (ha1.trans_le ht.1)).le)) (sq_nonneg _)
    rw [←intervalIntegral.integral_of_le hab]
    have hc : (∫ t in a..b, ‖deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t‖) =
        ∫ t in a..b, -g t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact hn t ht
    rw [hc,intervalIntegral.integral_neg]
    have hf : (∫ t in a..b, g t) = f b-f a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hg.intervalIntegrable_of_Icc hab)
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact hder t ht
    rw [hf]
    ring
  refine ⟨?_,hi,?_⟩
  · intro t ht
    simpa only [f,Complex.ofReal_div,Complex.ofReal_one] using
      (hder t ht).ofReal_comp.differentiableAt
  · have hlb : 1 ≤ Real.log b := hla.trans (Real.log_le_log
      (zero_lt_one.trans ha1) hab)
    rw [hint,norm_div,norm_div,norm_one,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (zero_le_one.trans hla),Real.norm_of_nonneg (zero_le_one.trans hlb)]
    have hfa : f a ≤ 1 := by
      simpa only [f,div_one] using one_div_le_one_div_of_le zero_lt_one hla
    have hfb : 0 ≤ f b := by dsimp [f]; positivity
    dsimp [f] at *
    linarith

lemma angularKummerCharacter_norm_le_one (ℓ : ℤ) (v : Eisenstein)
    {p : Eisenstein} (hp : primary p) : ‖angularKummerCharacter ℓ v p‖ ≤ 1 := by
  rw [angularKummerCharacter,norm_mul,norm_theta (primary_ne_zero hp),one_mul]
  exact norm_cubicSymbol_le_one hp v

/-- The unweighted prime estimate is derived from the raw published
Chebyshev error; it is not an additional analytic input. -/
theorem angular_kummer_prime_logSaving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A →
      ‖primeCutoffSum (angularKummerCharacter ℓ v) X‖ ≤ C*X/(Real.log X)^D := by
  obtain ⟨C,Y₀,hC,hY₀,hbound⟩ := weighted_angular_kummer_prime_log_bound hEF ℓ hℓ
    (2*A) (2*D) (by positivity) (by positivity)
  have hroot := Real.tendsto_sqrt_atTop.eventually_ge_atTop (max Y₀ (Real.exp 1))
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp
    (((hroot.and (sqrt_logSq_logSaving D)).and
      (Real.tendsto_log_atTop.eventually_ge_atTop 4)).and (eventually_gt_atTop (1:ℝ)))
  refine ⟨18+3*C,max X₀ 2,by positivity,by simp,?_⟩
  intro X hX v hv hnc hNv
  obtain ⟨⟨⟨hr,hs⟩,hlog⟩,hX1⟩ := hX₀ X ((le_max_left _ _).trans hX)
  have hXp : 0 < X := zero_lt_one.trans hX1
  have hLp : 0 < Real.log X := by linarith
  have hsp : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXp
  have hsY : Y₀ ≤ Real.sqrt X := (le_max_left _ _).trans hr
  have hse : Real.exp 1 ≤ Real.sqrt X := (le_max_right _ _).trans hr
  have hsX : Real.sqrt X ≤ X := Real.sqrt_le_self_iff.mpr (Or.inr hX1.le)
  have hls : Real.log (Real.sqrt X) = Real.log X/2 := Real.log_sqrt hXp.le
  have hls1 : 1 ≤ Real.log (Real.sqrt X) := by rw [hls]; linarith
  have hbase : Real.log X ≤ (Real.log (Real.sqrt X))^2 := by rw [hls]; nlinarith
  have hpow (E : ℝ) (hE : 0 ≤ E) : (Real.log X)^E ≤ (Real.log (Real.sqrt X))^(2*E) := by
    calc
      _ ≤ ((Real.log (Real.sqrt X))^2)^E := Real.rpow_le_rpow hLp.le hbase hE
      _ = _ := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_natCast_mul (zero_le_one.trans hls1) 2 E).symm
  have hcon : norm v ≤ (Real.log (Real.sqrt X))^(2*A) := hNv.trans (hpow A hA.le)
  obtain ⟨hd,hi,hvar⟩ := reciprocal_log_variation hse hsX
  have hlarge := hbound (Real.sqrt X) X hsY hsX v hv hnc hcon (fun _ => 1) hd hi
  have hbig : ‖∑ p ∈ (primeCutoff X).filter (fun p => Real.sqrt X < norm p),
      angularKummerCharacter ℓ v p‖ ≤ 3*C*X/(Real.log X)^D := by
    simp only [one_mul] at hlarge
    apply hlarge.trans
    calc
      _ ≤ (C*X/(Real.log (Real.sqrt X))^(2*D))*3 :=
        mul_le_mul_of_nonneg_left hvar (by positivity)
      _ ≤ (C*X/(Real.log X)^D)*3 :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity)
            (Real.rpow_pos_of_pos hLp D) (hpow D hD.le)) (by norm_num)
      _ = _ := by ring
  have hsmall : ‖primeCutoffSum (angularKummerCharacter ℓ v) (Real.sqrt X)‖ ≤
      18*X/(Real.log X)^D := by
    rw [primeCutoffSum_eq_sum]
    have hcard := primary_support_card_le (primeCutoff (Real.sqrt X)) hsp.le
      (fun p hp => ⟨(mem_primeCutoff.mp hp).1.1,(mem_primeCutoff.mp hp).2⟩)
    have hsq : Real.sqrt X ≤ X/(Real.log X)^D := by
      have hx : Real.sqrt X ≤ Real.sqrt X*(Real.log X)^2 :=
        le_mul_of_one_le_right hsp.le (one_le_pow₀ (by linarith))
      exact hx.trans hs
    calc
      _ ≤ ∑ _p ∈ primeCutoff (Real.sqrt X), (1:ℝ) := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun p hp => angularKummerCharacter_norm_le_one ℓ v
          (mem_primeCutoff.mp hp).1.1)
      _ = ((primeCutoff (Real.sqrt X)).card:ℝ) := by simp
      _ ≤ 18*Real.sqrt X := hcard
      _ ≤ 18*(X/(Real.log X)^D) := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = _ := by ring
  have hsplit : primeCutoffSum (angularKummerCharacter ℓ v) X =
      primeCutoffSum (angularKummerCharacter ℓ v) (Real.sqrt X)+
        ∑ p ∈ (primeCutoff X).filter (fun p => Real.sqrt X < norm p),
          angularKummerCharacter ℓ v p := by
    rw [primeCutoffSum_eq_sum,primeCutoffSum_eq_sum]
    have he : (primeCutoff X).filter (fun p => ¬Real.sqrt X < norm p) =
        primeCutoff (Real.sqrt X) := by
      ext p
      simp only [Finset.mem_filter,mem_primeCutoff,not_lt]
      constructor
      · rintro ⟨⟨hp,_⟩,hs⟩; exact ⟨hp,hs⟩
      · rintro ⟨hp,hs⟩; exact ⟨⟨hp,hs.trans hsX⟩,hs⟩
    rw [←he]
    exact (Finset.sum_filter_add_sum_filter_not (primeCutoff X)
      (fun p => Real.sqrt X < norm p) _).symm.trans (add_comm _ _)
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add hsmall hbig).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
