import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortTheorem
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLiouvilleDistance

namespace OAI

/-! The all-scale Liouville specialization under the quantitative
character-distance hypothesis. -/

namespace TwoPointCorrelations

open Filter Finset

theorem mrt_liouville_short_of_distance (hMRT : MRTShortExponentialInput)
    (hdistance : ∃ K : ℝ, 0≤K ∧ ∀ᶠ X : ℕ in atTop,
      ∀ q : ℕ, 0<q → (q:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t|≤X →
        (1/10:ℝ)*Real.log (Real.log (X:ℝ))-K ≤
          squaredDistance liouville (characterTwist χ t) X) :
    MRTLiouvilleShortInput := by
  obtain ⟨C,hC,hmean⟩ := hMRT
  obtain ⟨K,hK,hd⟩ := hdistance
  have hlog : Tendsto (fun X:ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp
    (hd.and (hlog.eventually (eventually_ge_atTop (1:ℝ))))
  let B : ℝ := max 10 (X₀:ℝ)
  let D : ℝ := Real.log B/Real.log (Real.log (10:ℝ))
  have hB : 10≤B := le_max_left _ _
  have hD : 0≤D := div_nonneg (Real.log_nonneg (by linarith))
    halasz_loglog_ten_pos.le
  refine ⟨C*(Real.exp (K/20)+1)+D+1,by positivity,?_⟩
  intro X H hH hHX α
  have hδ := mrt_short_error_nonneg hH hHX
  have hratio : 0≤Real.log (Real.log (H:ℝ))/Real.log H :=
    div_nonneg (Real.log_nonneg (mrt_allowed_short_log hH)) (by
      have hh := mrt_allowed_short_log hH
      linarith)
  by_cases hX : X₀≤X
  · obtain ⟨hXdist,hLX⟩ := hX₀ X hX
    let M := (1/10:ℝ)*Real.log (Real.log (X:ℝ))-K
    have hdist : MRTDistanceLowerBound liouville X H M := by
      intro q hq hqQ χ t ht
      apply hXdist q hq _ χ t ht
      exact hqQ.trans (min_le_left _ _)
    have heq : Real.exp (-M/20) =
        Real.exp (K/20)*(Real.log (X:ℝ))^(-1/200:ℝ) := by
      rw [Real.rpow_def_of_pos (by linarith : 0<Real.log (X:ℝ)),← Real.exp_add]
      congr 1
      dsimp [M]
      ring
    have hp : (Real.log (X:ℝ))^(-1/200:ℝ) ≤
        (Real.log (X:ℝ))^(-1/700:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hLX (by norm_num)
    have herr : Real.exp (-M/20)+mrtShortError X H ≤
        (Real.exp (K/20)+1)*mrtShortError X H := by
      rw [heq]
      have hh := mul_le_mul_of_nonneg_left hp (Real.exp_pos (K/20)).le
      have hr : (Real.log (X:ℝ))^(-1/700:ℝ) ≤ mrtShortError X H := by
        unfold mrtShortError
        linarith
      have hh' := mul_le_mul_of_nonneg_left hr (Real.exp_pos (K/20)).le
      nlinarith
    have hm := hmean X H hH hHX liouville liouville_multiplicative
      liouville_oneBounded M hdist α
    calc
      _ ≤ C*(H:ℝ)*X*((Real.exp (K/20)+1)*mrtShortError X H) :=
        hm.trans (mul_le_mul_of_nonneg_left herr (by positivity))
      _ = (C*(Real.exp (K/20)+1))*(H:ℝ)*X*mrtShortError X H := by ring
      _ ≤ _ := by gcongr; linarith
  · have hHB : (H:ℝ)≤B := by
      apply le_trans _ (le_max_right _ _)
      exact_mod_cast hHX.trans (le_of_not_ge hX)
    have hm := halasz_short_bounded_length liouville liouville_oneBounded
      X H hB hH hHB α
    have hr : Real.log (Real.log (H:ℝ))/Real.log H ≤ mrtShortError X H := by
      unfold mrtShortError
      exact le_add_of_nonneg_right (Real.rpow_nonneg
        (Real.log_nonneg (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))) _)
    calc
      _ ≤ D*(X:ℝ)*H*mrtShortError X H :=
        hm.trans (mul_le_mul_of_nonneg_left hr (by positivity))
      _ = D*(H:ℝ)*X*mrtShortError X H := by ring
      _ ≤ _ := by gcongr; nlinarith [Real.exp_pos (K/20)]

theorem mrt_liouville_short_of_prime_tail
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) (K : ℝ)
    (htail : ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0<q →
      (q:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t|≤X →
        -K ≤ (∑ p ∈ mrtLiouvillePrimeTail X,
          characterTwist χ t p/((p:ℝ):ℂ)).re) :
    MRTLiouvilleShortInput := by
  exact mrt_liouville_short_of_distance
    (mrt_short_exponential_of_prime_estimates hprime hhigh)
    (mrt_liouville_distance_from_prime_tail K htail)

end TwoPointCorrelations

end OAI
