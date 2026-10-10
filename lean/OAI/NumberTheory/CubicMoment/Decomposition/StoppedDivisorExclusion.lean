import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCharacterRows

namespace OAI

/-! Divisibility filters in the coprime Mellin rows are finite combinations
of the original coprimality exclusions. This identity keeps the stopped
coefficient unchanged, so its proved Kummer estimate remains applicable. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_subset_exclusion_count (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) :
    (U.powerset.card:ℝ) ≤ 18*norm (∏ p ∈ U,p) := by
  have hprod : primary (∏ p ∈ U,p) :=
    primary_finset_prod U (fun p => p) (fun p hp => (hU p hp).1)
  have hcard : U.powerset.card ≤ (primaryElementBall (norm (∏ p ∈ U,p))).card := by
    apply Finset.card_le_card_of_injOn (fun s : Finset Eisenstein => ∏ p ∈ s,p)
    · intro s hs
      have hsub := Finset.mem_powerset.mp hs
      exact mem_primaryElementBall.mpr
        ⟨primary_finset_prod s (fun p => p) (fun p hp => (hU p (hsub hp)).1),
          norm_le_of_dvd (primary_ne_zero hprod)
            (Finset.prod_dvd_prod_of_subset s U (fun p => p) hsub)⟩
    · exact primaryPrimeFactors_prod_injective hU
  exact (Nat.cast_le.mpr hcard).trans (primaryElementBall_card_le (norm_nonneg _))

theorem prime_product_divisibility_exclusions (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (n : Eisenstein) :
    (if (∏ p ∈ U,p) ∣ n then (1:ℂ) else 0) =
      ∑ s ∈ U.powerset, (-1:ℂ)^s.card*
        (if IsCoprime n (∏ p ∈ s,p) then 1 else 0) := by
  have hd : (∏ p ∈ U,p) ∣ n ↔ ∀ p ∈ U,p ∣ n := by
    constructor
    · intro hd p hp
      exact (Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp).trans hd
    · intro hd
      apply Finset.prod_dvd_of_coprime _ hd
      intro p hp q hq hpq
      exact primaryPrimes_isCoprime (hU p hp) (hU q hq) hpq
  have hpoint (p : Eisenstein) (hp : p ∈ U) :
      (if p ∣ n then (1:ℂ) else 0) = 1-(if IsCoprime n p then 1 else 0) := by
    have hc : IsCoprime n p ↔ ¬p ∣ n := by
      rw [isCoprime_comm]
      exact (hU p hp).2.irreducible.coprime_iff_not_dvd
    by_cases hp : p ∣ n <;> simp [hp,hc]
  calc
    _ = ∏ p ∈ U, (if p ∣ n then (1:ℂ) else 0) := by simp only [Finset.prod_boole,hd]
    _ = ∏ p ∈ U, (1-(if IsCoprime n p then (1:ℂ) else 0)) :=
      Finset.prod_congr rfl hpoint
    _ = _ := by
      rw [Finset.prod_sub]
      simp only [Finset.prod_const_one,mul_one,Finset.prod_boole,
        ←IsCoprime.prod_right_iff]

theorem prime_product_filtered_sum (S U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (F : Eisenstein → ℂ) :
    (∑ n ∈ S.filter (fun n => (∏ p ∈ U,p) ∣ n), F n) =
      ∑ s ∈ U.powerset, (-1:ℂ)^s.card*
        ∑ n ∈ S.filter (fun n => IsCoprime n (∏ p ∈ s,p)), F n := by
  simp only [Finset.sum_filter]
  calc
    _ = ∑ n ∈ S, (if (∏ p ∈ U,p) ∣ n then (1:ℂ) else 0)*F n := by
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> simp
    _ = ∑ n ∈ S, (∑ s ∈ U.powerset, (-1:ℂ)^s.card*
        (if IsCoprime n (∏ p ∈ s,p) then 1 else 0))*F n := by
      simp_rw [prime_product_divisibility_exclusions U hU]
    _ = _ := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedIntervalSupport_filter_coprime (X a b : ℝ) (e q : Eisenstein) :
    (stoppedIntervalSupport ι X a b e).filter (fun n => IsCoprime n q) =
      stoppedIntervalSupport ι X a b (e*q) := by
  ext n
  have hc : IsCoprime n (e*q) ↔ IsCoprime n e ∧ IsCoprime n q :=
    ⟨fun h => ⟨h.of_mul_right_left,h.of_mul_right_right⟩,fun h => h.1.mul_right h.2⟩
  simp only [stoppedIntervalSupport,Finset.mem_filter,hc]
  tauto

theorem stopped_divisibility_row (X w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (v e : Eisenstein)
    (U : Finset Eisenstein) (hU : ∀ p ∈ U, primaryPrime p) :
    (∑ n ∈ (stoppedIntervalSupport ι X a b e).filter
        (fun n => (∏ p ∈ U,p) ∣ n),
      stoppedRowCoefficient X w z u W selected n*cubicSymbol n v) =
      ∑ s ∈ U.powerset, (-1:ℂ)^s.card*
        stoppedCharacterSum X w z a b u W selected v (e*(∏ p ∈ s,p)) := by
  rw [prime_product_filtered_sum _ U hU]
  apply Finset.sum_congr rfl
  intro s _
  rw [stoppedIntervalSupport_filter_coprime,←stoppedCharacterSum_row]

theorem stopped_small_divisor_sw (hpnt : PrimaryPrimePNT)
    (hSW : KummerPrimeSiegelWalfisz)
    {ξ κ A D H E F J L d : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ a b u V : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ a → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ U : Finset Eisenstein, (∀ p ∈ U, primaryPrime p) →
      norm (∏ p ∈ U,p) ≤ (Real.log X)^L → norm (∏ p ∈ U,p) ≤ X^d →
      ∀ (j k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ (stoppedIntervalSupport ι X a b e).filter (fun n => (∏ p ∈ U,p) ∣ n),
        stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j k h Z Q early) n*cubicSymbol n v‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨K,hK,hbound⟩ := stopped_sequence_kummer_sw (ι := ι)
    (D := D+L) (E := E+d) hpnt hSW hξ hξz hκ hA (by linarith) hH hF hJ
  refine ⟨18*K,by positivity,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ)] with X hbound hX
  intro δ a b u V hδ hδone hwidth ha hb hbX hV hu hVF W hW hWi hWd
    v e hv hnc hNv he hNe U hU hUL hUX j k h Z Q early
  have hXp : 0 < X := zero_lt_one.trans hX
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hbp : 0 < b := (Real.rpow_pos_of_pos hXp κ).trans_le hb
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j k h Z Q early
  have hterm (s : Finset Eisenstein) (hs : s ∈ U.powerset) :
      ‖(-1:ℂ)^s.card*stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) a b u W
        selected v (e*(∏ p ∈ s,p))‖ ≤ K*b/(Real.log X)^(D+L) := by
    have hp : primary (∏ p ∈ s,p) := primary_finset_prod s (fun p => p)
      (fun p hp => (hU p (Finset.mem_powerset.mp hs hp)).1)
    have hpU : primary (∏ p ∈ U,p) := primary_finset_prod U (fun p => p)
      (fun p hp => (hU p hp).1)
    have hn : norm (∏ p ∈ s,p) ≤ X^d :=
      (norm_le_of_dvd (primary_ne_zero hpU)
        (Finset.prod_dvd_prod_of_subset s U (fun p => p) (Finset.mem_powerset.mp hs))).trans hUX
    have hn' : norm (e*(∏ p ∈ s,p)) ≤ X^(E+d) := by
      rw [norm_mul_eq,Real.rpow_add hXp]
      exact mul_le_mul hNe hn (norm_nonneg _) (Real.rpow_nonneg hXp.le _)
    simpa only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul] using
      hbound δ a b u V hδ hδone hwidth ha hb hbX hV hu hVF W hW hWi hWd
        v (e*(∏ p ∈ s,p)) hv hnc hNv (mul_ne_zero he (primary_ne_zero hp)) hn' j k h Z Q early
  rw [stopped_divisibility_row _ _ _ _ _ _ _ selected v e U hU]
  calc
    _ ≤ ∑ s ∈ U.powerset, ‖(-1:ℂ)^s.card*
        stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) a b u W selected v (e*(∏ p ∈ s,p))‖ :=
      norm_sum_le _ _
    _ ≤ (U.powerset.card:ℝ)*(K*b/(Real.log X)^(D+L)) := by
      exact (Finset.sum_le_sum hterm).trans_eq (by rw [Finset.sum_const,nsmul_eq_mul])
    _ ≤ (18*(Real.log X)^L)*(K*b/(Real.log X)^(D+L)) :=
      mul_le_mul_of_nonneg_right ((prime_subset_exclusion_count U hU).trans
        (mul_le_mul_of_nonneg_left hUL (by norm_num))) (by positivity)
    _ = _ := by rw [Real.rpow_add hlog]; field_simp

end CubicFirstMoment

end

end OAI
