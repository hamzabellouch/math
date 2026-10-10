import Mathlib
import OAI.NumberTheory.CubicGram.GlobalRecurrence

namespace OAI

/-! Compact sieve majorants and common-factor energy bounds. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryCharacterGram_one_one_bound (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : Continuous W) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 0 < Z → ‖primaryCharacterGram 1 1 W Z‖ ≤ C*Z := by
  obtain ⟨R,hR,hR0⟩ := hW.exists_pos_le_norm
  obtain ⟨L,hL⟩ := hW'.bounded_above_of_compact_support hW
  let K := max L 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hLK : L ≤ K := le_max_left _ _
  refine ⟨18*R*K,by positivity,?_⟩
  intro Z hZ
  have hs : primaryCharacterGram 1 1 W Z =
      ∑ n ∈ nonzeroNormBall (R*Z), if primary n then
        W (norm n/Z)*cubicSymbol 1 n*star (cubicSymbol 1 n) else 0 := by
    apply tsum_eq_sum
    intro n hn
    split_ifs with hp
    · have hn' : R*Z < norm n := lt_of_not_ge (fun h =>
        hn (mem_nonzeroNormBall.mpr ⟨h,primary_ne_zero hp⟩))
      have hw : W (norm n/Z) = 0 := hR0 _ (by
        rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) (le_of_lt hZ))]
        exact (le_div_iff₀ hZ).mpr hn'.le)
      simp [hw]
    · rfl
  rw [hs]
  calc
    _ ≤ ∑ n ∈ nonzeroNormBall (R*Z),
        ‖if primary n then W (norm n/Z)*cubicSymbol 1 n*star (cubicSymbol 1 n) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ nonzeroNormBall (R*Z), K := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs with hp
      · rw [norm_mul,norm_mul,norm_star]
        calc
          _ ≤ ‖W (norm n/Z)‖*1*1 := by
            gcongr <;> exact norm_cubicSymbol_le_one primary_one n
          _ ≤ K := by simpa using (hL (norm n/Z)).trans hLK
      · simpa using hK.le
    _ = (nonzeroNormBall (R*Z)).card*K := by simp
    _ ≤ (18*(R*Z))*K := mul_le_mul_of_nonneg_right (nonzeroNormBall_card_le (by positivity)) hK.le
    _ = _ := by ring

def cubicSieveCutoff (t : ℝ) : ℂ := gramLogBump t

lemma cubicSieveCutoff_compact : HasCompactSupport cubicSieveCutoff :=
  gramLogBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

lemma cubicSieveCutoff_smooth : ContDiff ℝ ∞ cubicSieveCutoff :=
  Complex.ofRealCLM.contDiff.comp gramLogBump.contDiff

lemma cubicSieveCutoff_zero {t : ℝ} (ht : 2 ≤ |t|) : cubicSieveCutoff t = 0 := by
  have h := gramLogBump.zero_of_le_dist (x := t)
  have he : gramLogBump t = 0 := h (by
    simpa only [Real.dist_eq,sub_zero,gramLogBump] using ht)
  simp [cubicSieveCutoff,he]

lemma cubicSieveCutoff_one {t : ℝ} (ht : |t| ≤ 1) : cubicSieveCutoff t = 1 := by
  have he : gramLogBump t = 1 := gramLogBump.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,gramLogBump] using ht)
  simp [cubicSieveCutoff,he]

lemma primarySmoothedSieveMass_cutoff (S : Finset Eisenstein) (u : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 < M) :
    primarySmoothedSieveMass S u cubicSieveCutoff M =
      ∑ x ∈ nonzeroNormBall (2*M), if primary x then
        cubicSieveCutoff (norm x/M)*(‖∑ n ∈ S, u n*cubicSymbol n x‖^2 : ℝ) else 0 := by
  apply tsum_eq_sum
  intro x hx
  split_ifs with hp
  · have hn : 2*M < norm x := lt_of_not_ge (fun h =>
      hx (mem_nonzeroNormBall.mpr ⟨h,primary_ne_zero hp⟩))
    have hw : cubicSieveCutoff (norm x/M) = 0 := cubicSieveCutoff_zero (by
      rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hM.le)]
      exact (le_div_iff₀ hM).mpr hn.le)
    simp [hw]
  · rfl

lemma finiteCubicMass_le_smoothed (S H : Finset Eisenstein)
    (hH : ∀ x ∈ H, primary x) (u : Eisenstein → ℂ) {M : ℝ} (hM : 0 < M)
    (hHM : ∀ x ∈ H, norm x ≤ M) :
    (∑ x ∈ H, ‖∑ n ∈ S, u n*cubicSymbol n x‖^2) ≤
      ‖primarySmoothedSieveMass S u cubicSieveCutoff M‖ := by
  have hsub : H ⊆ nonzeroNormBall (2*M) := by
    intro x hx
    exact mem_nonzeroNormBall.mpr ⟨(hHM x hx).trans (by linarith),primary_ne_zero (hH x hx)⟩
  have hreal := (Complex.re_le_norm (primarySmoothedSieveMass S u cubicSieveCutoff M))
  apply le_trans _ hreal
  rw [primarySmoothedSieveMass_cutoff S u hM,Complex.re_sum]
  have he (x : Eisenstein) (hx : x ∈ H) :
      (if primary x then cubicSieveCutoff (norm x/M)*
        (‖∑ n ∈ S, u n*cubicSymbol n x‖^2 : ℝ) else 0).re =
        ‖∑ n ∈ S, u n*cubicSymbol n x‖^2 := by
    rw [ite_eq_left (hH x hx),cubicSieveCutoff_one]
    · norm_cast; simp
    · rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hM.le)]
      exact (div_le_one hM).mpr (hHM x hx)
  rw [← Finset.sum_congr rfl he]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro x hx hxH
  split_ifs
  · simp only [cubicSieveCutoff,← Complex.ofReal_mul,Complex.ofReal_re]
    exact mul_nonneg gramLogBump.nonneg (sq_nonneg _)
  · simp

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrimeFactors_subset_of_dvd {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hab : a ∣ b) : primaryPrimeFactors a ⊆ primaryPrimeFactors b := by
  intro p hp
  obtain ⟨hpp,hpa⟩ := primaryPrimeFactor_spec ha hp
  exact primaryPrime_mem_factors hb hpp (hpa.trans hab)

lemma primary_divisors_card_le (T : Finset Eisenstein)
    (hT : ∀ k ∈ T, primary k ∧ Squarefree k) {p : Eisenstein} (hp : primary p) :
    ((T.filter (· ∣ p)).card : ℝ) ≤ (2 : ℝ)^(primaryPrimeFactors p).card := by
  have hmaps : ∀ k ∈ T.filter (· ∣ p), primaryPrimeFactors k ∈ (primaryPrimeFactors p).powerset := by
    intro k hk
    rw [Finset.mem_filter] at hk
    exact Finset.mem_powerset.mpr (primaryPrimeFactors_subset_of_dvd (hT k hk.1).1 hp hk.2)
  have hinj : Set.InjOn primaryPrimeFactors (↑(T.filter (· ∣ p)) : Set Eisenstein) := by
    intro k hk l hl he
    have hk' := hT k (Finset.mem_filter.mp hk).1
    have hl' := hT l (Finset.mem_filter.mp hl).1
    rw [← primaryPrimeFactors_prod hk'.1 hk'.2,← primaryPrimeFactors_prod hl'.1 hl'.2,he]
  have hc := (Finset.card_image_iff.mpr hinj).symm.le.trans
    (Finset.card_le_card (Finset.image_subset_iff.mpr hmaps))
  rw [Finset.card_powerset] at hc
  exact_mod_cast hc

lemma residualRows_sum_image (S : Finset Eisenstein) {k : Eisenstein} (hk : k ≠ 0)
    (f : Eisenstein → ℝ) :
    (∑ a ∈ residualRows S k, f (k*a)) = ∑ p ∈ S, if k ∣ p then f p else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun a _ => k*a)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨(mem_residualRows hk).mp ha, dvd_mul_right _ _⟩
  · intro a ha b hb hab
    exact mul_left_cancel₀ hk hab
  · intro p hp
    obtain ⟨a,rfl⟩ := (Finset.mem_filter.mp hp).2
    exact ⟨a,(mem_residualRows hk).mpr (Finset.mem_filter.mp hp).1,rfl⟩
  · intro a ha
    rfl

lemma common_energy_cubic_weight (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ) :
    (∑ k ∈ commonRowFactors S, (2 : ℝ)^(primaryPrimeFactors k).card *
      commonBlockEnergy S u k) ≤
      ∑ p ∈ S, ((2 : ℝ)^(primaryPrimeFactors p).card)^3 * ‖u p‖^2 := by
  have hT (k : Eisenstein) (hk : k ∈ commonRowFactors S) := commonRowFactors_spec hS hk
  have hw (k : Eisenstein) (hk : k ∈ commonRowFactors S) :
      (2 : ℝ)^(primaryPrimeFactors k).card * commonBlockEnergy S u k ≤
        ∑ p ∈ S, if k ∣ p then ((2 : ℝ)^(primaryPrimeFactors p).card)^2 * ‖u p‖^2 else 0 := by
    rw [← residualRows_sum_image S (primary_ne_zero (hT k hk).1)]
    unfold commonBlockEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hpS := (mem_residualRows (primary_ne_zero (hT k hk).1)).mp ha
    have hp := (hS (k*a) hpS).1
    have haa := (residualRows_primary (hT k hk).1 hS a ha).1
    have hka : (2 : ℝ)^(primaryPrimeFactors k).card ≤ (2 : ℝ)^(primaryPrimeFactors (k*a)).card :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_card
        (primaryPrimeFactors_subset_of_dvd (hT k hk).1 hp (dvd_mul_right _ _)))
    have haa' : (2 : ℝ)^(primaryPrimeFactors a).card ≤ (2 : ℝ)^(primaryPrimeFactors (k*a)).card :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_card
        (primaryPrimeFactors_subset_of_dvd haa hp (dvd_mul_left _ _)))
    calc
      _ = ((2 : ℝ)^(primaryPrimeFactors k).card*(2 : ℝ)^(primaryPrimeFactors a).card)*‖u (k*a)‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul hka haa' (by positivity) (by positivity)]) (sq_nonneg _)
  calc
    _ ≤ ∑ k ∈ commonRowFactors S, ∑ p ∈ S,
        if k ∣ p then ((2 : ℝ)^(primaryPrimeFactors p).card)^2 * ‖u p‖^2 else 0 :=
      Finset.sum_le_sum hw
    _ = ∑ p ∈ S, ((commonRowFactors S).filter (· ∣ p)).card *
        (((2 : ℝ)^(primaryPrimeFactors p).card)^2 * ‖u p‖^2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter]
      simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hc := primary_divisors_card_le (commonRowFactors S)
        (fun k hk => ⟨(hT k hk).1,(hT k hk).2⟩) (hS p hp).1
      calc
        _ ≤ (2 : ℝ)^(primaryPrimeFactors p).card *
            (((2 : ℝ)^(primaryPrimeFactors p).card)^2 * ‖u p‖^2) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by ring

theorem common_energy_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (X : ℝ),
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ X) →
      (∑ k ∈ commonRowFactors S, (2 : ℝ)^(primaryPrimeFactors k).card *
        commonBlockEnergy S u k) ≤ C * X^ε * ∑ a ∈ S, ‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := primeDivisorWeight_small_power (ε/3) (by positivity)
  refine ⟨C^3,by positivity,?_⟩
  intro S u X hS
  apply (common_energy_cubic_weight S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) u).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h := pow_le_pow_left₀ (by positivity) (hbound a (hS a ha).1 (hS a ha).2.1) 3
  have he : (norm a ^ (ε/3))^3 = norm a ^ ε := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg a)]
    congr 1
    norm_num
  rw [mul_pow,he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg a) (hS a ha).2.2 hε.le) (by positivity))

end CubicFirstMoment
end
end

end OAI
