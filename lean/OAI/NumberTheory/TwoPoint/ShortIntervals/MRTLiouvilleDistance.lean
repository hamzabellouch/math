import OAI.NumberTheory.TwoPoint.Basic
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmoothDistance
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeTailMass

namespace OAI

/-! Finite prime identities in the Liouville specialization of MRT,
including the reduction to the uniform lower bound for the real part of
the character prime sum in (1.12) of arXiv:1503.05121v3. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped ComplexConjugate Classical

lemma mrt_liouville_prime {p : ℕ} (hp : p.Prime) : liouville p = -1 := by
  simp [liouville,ArithmeticFunction.liouville_apply hp.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp]

lemma mrt_characterTwist_pow {q : ℕ} (χ : DirichletCharacter ℂ q)
    {k : ℕ} (hk : k≠0) (t : ℝ) (n : ℕ) :
    characterTwist (χ^k) ((k:ℝ)*t) n = (characterTwist χ t n)^k := by
  simp only [characterTwist,MulChar.pow_apply' χ hk,mul_pow]
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

lemma mrt_prime_sum_real (S : Finset ℕ) (g : ℕ → ℂ) :
    (∑ p ∈ S, (1+(g p).re)/(p:ℝ)) =
      (∑ p ∈ S, 1/(p:ℝ))+(∑ p ∈ S, g p/((p:ℝ):ℂ)).re := by
  simp only [Complex.re_sum,Complex.div_ofReal_re,← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  ring

lemma mrt_liouville_distance_sum (g : ℕ → ℂ) (N : ℕ) :
    squaredDistance liouville g N =
      ∑ p ∈ primesUpTo N, (1+(g p).re)/(p:ℝ) := by
  unfold squaredDistance
  apply sum_congr rfl
  intro p hp
  rw [mrt_liouville_prime (mem_filter.mp hp).2]
  simp

lemma mrt_liouville_distance_prime_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (N : ℕ) :
    squaredDistance liouville (characterTwist χ t) N =
      (∑ p ∈ primesUpTo N, 1/(p:ℝ))+
        (∑ p ∈ primesUpTo N, characterTwist χ t p/((p:ℝ):ℂ)).re := by
  rw [mrt_liouville_distance_sum,mrt_prime_sum_real]

lemma mrt_liouville_distance_band_lower {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (N : ℕ) (P : ℝ) :
    (∑ p ∈ mrtPrimeBand P N, 1/(p:ℝ))+
      (∑ p ∈ mrtPrimeBand P N, characterTwist χ t p/((p:ℝ):ℂ)).re ≤
        squaredDistance liouville (characterTwist χ t) N := by
  rw [mrt_liouville_distance_sum,← mrt_prime_sum_real]
  apply sum_le_sum_of_subset_of_nonneg
  · rw [mrtPrimeBand,mrt_sievePrimesUpTo_nat]
    exact sdiff_subset
  · intro p _ _
    apply div_nonneg _ (Nat.cast_nonneg p)
    have hr := (abs_le.mp ((Complex.abs_re_le_norm (characterTwist χ t p)).trans
      (characterTwist_norm_le_one χ t p))).1
    linarith

noncomputable def mrtLiouvillePrimeTail (X : ℕ) : Finset ℕ :=
  mrtPrimePowerTail (3/4) X

/-- Mertens supplies a quarter of log log X on the exact VK tail. -/
theorem mrt_liouville_prime_tail_mass :
    ∃ C : ℝ, 0≤C ∧ ∀ X : ℕ, 1≤Real.log (X:ℝ) →
      (1/4:ℝ)*Real.log (Real.log (X:ℝ))-C ≤
        ∑ p ∈ mrtLiouvillePrimeTail X, 1/(p:ℝ) := by
  obtain ⟨C,hC,hm⟩ := mrt_prime_power_tail_mass
  refine ⟨C,hC,?_⟩
  intro X hL
  simpa only [mrtLiouvillePrimeTail,show (1-(3/4:ℝ))=1/4 by norm_num] using
    hm (3/4) (by norm_num) (by norm_num) X hL

/-- A character prime-tail lower bound yields the Liouville
pretentious-distance estimate. -/
theorem mrt_liouville_distance_from_prime_tail (K : ℝ)
    (htail : ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0<q →
      (q:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t|≤X →
        -K ≤ (∑ p ∈ mrtLiouvillePrimeTail X,
          characterTwist χ t p/((p:ℝ):ℂ)).re) :
    ∃ K' : ℝ, 0≤K' ∧ ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0<q →
      (q:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t|≤X →
        (1/10:ℝ)*Real.log (Real.log (X:ℝ))-K' ≤
          squaredDistance liouville (characterTwist χ t) X := by
  obtain ⟨C,hC,hm⟩ := mrt_liouville_prime_tail_mass
  have hlog : Tendsto (fun X:ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C+|K|,by positivity,?_⟩
  filter_upwards [htail,hlog.eventually (eventually_ge_atTop (1:ℝ))]
    with X ht hL
  intro q hq hqX χ t htx
  have hb := mrt_liouville_distance_band_lower χ t X
    (Real.exp ((Real.log (X:ℝ))^(3/4:ℝ)))
  change (∑ p ∈ mrtLiouvillePrimeTail X, 1/(p:ℝ))+
    (∑ p ∈ mrtLiouvillePrimeTail X, characterTwist χ t p/((p:ℝ):ℂ)).re ≤ _ at hb
  have hp := ht q hq hqX χ t htx
  have hh := hm X hL
  have hLL : 0≤Real.log (Real.log (X:ℝ)) := Real.log_nonneg hL
  linarith [le_abs_self K]

end TwoPointCorrelations

end OAI
