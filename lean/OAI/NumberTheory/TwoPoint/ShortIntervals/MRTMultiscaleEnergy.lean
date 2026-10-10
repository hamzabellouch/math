import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalEnergy
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCofactorMoment
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTAmplification

namespace OAI

/-! The actual typical-set polynomial on a later MRT frequency class.
The preceding short prime polynomial is large, while each current-bin
polynomial is small. Amplification is applied before extending the
cofactor energy to the whole frequency interval. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_restricted_product_sum_energy_local {ι : Type*} (J : Finset ι)
    (Q R : ι → ℝ → ℂ) (hR : ∀ j ∈ J, Continuous (R j)) (A : ι → ℝ)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hQ : ∀ j ∈ J, ∀ t ∈ E, ‖Q j t‖ ≤ A j) :
    (∫ t in E, ‖∑ j ∈ J, Q j t * R j t‖ ^ 2) ≤
      (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 * (∫ t in E, ‖R j t‖ ^ 2) := by
  have hi (j : ι) (hj : j ∈ J) := mrt_continuous_square_integrable (hR j hj) hT hE
  calc
    _ ≤ ∫ t in E, (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 * ‖R j t‖ ^ 2 := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        ((integrable_finsetSum J (fun j hj => (hi j hj).const_mul ((A j) ^ 2))).const_mul _)
      intro t ht
      apply (mrt_norm_sum_sq_le_card J (fun j => Q j t * R j t)).trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro j hj
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hQ j hj t ht) 2) (sq_nonneg _)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum J (fun j hj => (hi j hj).const_mul ((A j) ^ 2))]
      simp only [integral_const_mul]

theorem mrt_short_class_cofactor_energy (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {Y N : ℕ} (hY : 0 < Y) (hN : 0 < N)
    (hbin : P ⊆ Icc Y (2 * Y)) (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (F : ℕ → ℂ) (hF : OneBounded F) {u : ℝ} (hu : 1 ≤ u)
    (r : ℕ) (hpowlo : u ≤ (Y : ℝ) ^ r) (hpowhi : (Y : ℝ) ^ r ≤ u * Y)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V)
    {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖mrtExponentialPolynomial P
      (fun p => a p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtCofactorPolynomial Q F N u t‖ ^ 2) ≤
      (16 * Real.exp 10 * (T / (N : ℝ) + (2 : ℝ) ^ (r + 1) * Y) *
        (r.factorial : ℝ) ^ 2) / V ^ (2 * r) := by
  have hR : Continuous (mrtCofactorPolynomial Q F N u) := by
    have he : mrtCofactorPolynomial Q F N u =
        mrtExponentialPolynomial (Ioc ⌊(N : ℝ) / u⌋₊ ⌊(2 * N : ℝ) / u⌋₊)
          (fun n => (F n / ((finitePrimeDivisorCount Q n + 1 : ℕ) : ℂ)) / (n : ℂ))
          (fun n => -Real.log (n : ℝ)) :=
      funext (mrt_cofactor_exponential_polynomial Q F N hu)
    rw [he]
    exact mrtExponentialPolynomial_continuous _ _ _
  apply (mrt_amplified_energy _ _ (mrtExponentialPolynomial_continuous _ _ _) hR
    r hT.le hV hE hlarge).trans
  exact div_le_div_of_nonneg_right
    (mrt_short_prime_cofactor_moment P Q hP hY hN hbin a ha F hF hu r hpowlo hpowhi hT)
    (pow_nonneg hV.le _)

theorem mrt_typical_later_class_energy {ι κ : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P j, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (hlow : ∀ k ∈ K, 1 ≤ lower k)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    (hFb : OneBounded F) (Pprev : Finset ℕ) (hprev : ∀ p ∈ Pprev, p.Prime)
    {Y : ℕ} (hY : 0 < Y) (hprevbin : Pprev ⊆ Icc Y (2 * Y))
    (r : κ → ℕ) (hpowlo : ∀ k ∈ K, lower k ≤ (Y : ℝ) ^ r k)
    (hpowhi : ∀ k ∈ K, (Y : ℝ) ^ r k ≤ lower k * Y)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V) {E : Set ℝ}
    (hE : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤ ‖mrtExponentialPolynomial Pprev
      (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖)
    (A : κ → ℝ) (hsmall : ∀ k ∈ K, ∀ t ∈ E,
      ‖mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
        (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖ ≤ A k) :
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖ ^ 2) ≤
      384 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) +
      32 * Real.exp 10 * (K.card : ℝ) *
        ∑ k ∈ K, (A k) ^ 2 *
          ((T / (N : ℝ) + (2 : ℝ) ^ (r k + 1) * Y) *
            ((r k).factorial : ℝ) ^ 2 / V ^ (2 * r k)) := by
  let B := mrtTypicalCoefficient (J.erase j) P F
  let Q : κ → ℝ → ℂ := fun k =>
    mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
      (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ))
  let R : κ → ℝ → ℂ := fun k => mrtCofactorPolynomial (P j) B N (lower k)
  let D := mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N
  let G := mrtCoarsePolynomial (P j) (fun p => lower (bin p)) N (mrtTypicalCoefficient J P F)
  have hB : OneBounded B := mrtTypicalCoefficient_oneBounded _ _ _ hFb
  have hR (k : κ) (hk : k ∈ K) : Continuous (R k) := by
    have he : R k = mrtExponentialPolynomial
        (Ioc ⌊(N : ℝ) / lower k⌋₊ ⌊(2 * N : ℝ) / lower k⌋₊)
        (fun n => (B n / ((finitePrimeDivisorCount (P j) n + 1 : ℕ) : ℂ)) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) :=
      funext (mrt_cofactor_exponential_polynomial (P j) B N (hlow k hk))
    rw [he]
    exact mrtExponentialPolynomial_continuous _ _ _
  have hD : Continuous D := mrtExponentialPolynomial_continuous _ _ _
  have hG : Continuous G := mrtExponentialPolynomial_continuous _ _ _
  have hsum : G = fun t => ∑ k ∈ K, Q k t * R k t :=
    funext (mrt_typical_coarse_bins J P hP hdis hj K bin hbin lower N hδ hδ2 hL F hF)
  have hg' : (∫ t in E, ‖G t‖ ^ 2) ≤ 16 * Real.exp 10 * (K.card : ℝ) *
      ∑ k ∈ K, (A k) ^ 2 * ((T / (N : ℝ) + (2 : ℝ) ^ (r k + 1) * Y) *
        ((r k).factorial : ℝ) ^ 2 / V ^ (2 * r k)) := by
    rw [hsum]
    apply (mrt_restricted_product_sum_energy_local K Q R hR A hT.le hE hsmall).trans
    calc
      _ ≤ (K.card : ℝ) * ∑ k ∈ K, (A k) ^ 2 *
          ((16 * Real.exp 10 * (T / (N : ℝ) + (2 : ℝ) ^ (r k + 1) * Y) *
            ((r k).factorial : ℝ) ^ 2) / V ^ (2 * r k)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (mrt_short_class_cofactor_energy Pprev (P j) hprev hY hN hprevbin F
            (fun p hp => hFb p (hprev p hp).pos) B hB (hlow k hk) (r k)
            (hpowlo k hk) (hpowhi k hk) hT hV hE hlarge) (sq_nonneg _)
      _ = _ := by
        simp only [mul_sum]
        apply sum_congr rfl
        intro k _
        ring
  have herr := mrt_coarse_error_mean_square (P j) (hP j hj) (fun p => lower (bin p))
    hN hδ hδ2 hL (mrtTypicalCoefficient J P F)
    (mrtTypicalCoefficient_oneBounded J P F hFb) hT
  rw [mrtTypicalCoefficient_supported J P hj F] at herr
  change (∫ t in -T..T, ‖D t - G t‖ ^ 2) ≤ _ at herr
  apply (mrt_restricted_energy_split D G hD hG hT.le hE).trans
  calc
    _ ≤ 2 * (192 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1))) +
        2 * (16 * Real.exp 10 * (K.card : ℝ) *
          ∑ k ∈ K, (A k) ^ 2 * ((T / (N : ℝ) + (2 : ℝ) ^ (r k + 1) * Y) *
            ((r k).factorial : ℝ) ^ 2 / V ^ (2 * r k))) :=
      add_le_add (mul_le_mul_of_nonneg_left herr (by norm_num))
        (mul_le_mul_of_nonneg_left hg' (by norm_num))
    _ = _ := by ring

end TwoPointCorrelations

end OAI
