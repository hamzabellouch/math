import OAI.NumberTheory.JointDickman.Amplification.LowAdditionGeometry
import OAI.NumberTheory.JointDickman.Amplification.AdditionProgressionInterval

namespace OAI

/-! # The harmonic sieve for the decreasing quotient progression -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def lowAdditionProgressionWeight (B : ℕ) (g : ℝ)
    (e j b z₀ : ℕ) (c₀ : ℤ) (q : ℝ) (n : ℕ) : ℝ :=
  (∏ p ∈ primePrefix B g (auxiliaryPrimes B) \ additionExcludedPrimes B e b,
    residueWeight q 0 ((z₀ : ZMod p)+j*n)*residueWeight (1/2) 0 ((c₀ : ZMod p)-e*n))/
      ((z₀ : ℝ)+(j : ℝ)*n)

theorem lowAdditionProgressionWeight_nonneg {B e j b z₀ n : ℕ} {g q : ℝ} {c₀ : ℤ}
    (hq : 0 ≤ q) : 0 ≤ lowAdditionProgressionWeight B g e j b z₀ c₀ q n := by
  apply div_nonneg _ (by positivity)
  exact prod_nonneg (fun _ _ => mul_nonneg (residueWeight_nonneg _ _ hq)
    (residueWeight_nonneg _ _ (by norm_num)))

theorem low_addition_window_harmonic_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {κ g ε : ℝ} (hκ : 0 < κ) (hg : 0 < g) (hg1 : g < 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (e j b z₀ : ℕ) (c₀ : ℤ) (q W : ℝ),
        0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B →
        (e*b : ℕ) ≤ Real.exp (κ*B) → (e : ℤ)*z₀+(j : ℤ)*c₀ = b →
        0 ≤ q → q ≤ 1 → 2*(j : ℝ) ≤ W →
        (∑ n ∈ Ico (additionIntervalLower W j) (additionIntervalUpper W j),
          lowAdditionProgressionWeight B g e j b z₀ c₀ q n) ≤
          K/(j : ℝ)*Real.exp ((-(3/2-q)*g+ε)*auxiliaryLogLength B)+
            4*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W := by
  obtain ⟨K,hK,hbound⟩ := numeric_prefix_harmonic_bound hFord hM hκ hg hg1 hε
  refine ⟨10*K,by positivity,?_⟩
  filter_upwards [hbound] with B hB
  intro e j b z₀ c₀ q W he hb hj hcut hsize hbase hq hq1 hW
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hW0 : 0 < W := by linarith
  have hWhalf : 0 < W/2 := half_pos hW0
  have huv := additionInterval_order (j := j) hW0.le
  have hlen := additionInterval_length hj (by linarith : (j : ℝ) ≤ W)
  have hprod : (∏ p ∈ additionExcludedPrimes B e b, p : ℕ) ≤ Real.exp (κ*B) :=
    (by exact_mod_cast additionExcludedPrimes_product_le (B := B) he hb :
      ((∏ p ∈ additionExcludedPrimes B e b, p : ℕ) : ℝ) ≤ (e*b : ℕ)).trans hsize
  have hh := hB (additionExcludedPrimes B e b) z₀ j c₀ (-e) q (W/2)
    (additionIntervalLower W j) (additionIntervalUpper W j)
    (additionExcludedPrimes_subset B e b) hprod hq hq1 hWhalf huv
    (fun p hp => by simpa only [Int.cast_neg,Int.cast_natCast] using
      low_addition_progression_good_primes (g := g) he hb hj hcut hbase p hp)
    (fun n hn => by simpa only [Int.cast_natCast] using additionInterval_denominator hj hW hn)
  have hcoef : K*((additionIntervalUpper W j : ℝ)-additionIntervalLower W j)/(W/2) ≤
      (10*K)/(j : ℝ) := by
    calc
      _ ≤ K*(5*W/j)/(W/2) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlen hK.le) hWhalf.le
      _ = _ := by field_simp; ring
  have herr : 2*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/(W/2) =
      4*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W := by ring
  rw [herr] at hh
  have hfinal := hh.trans (add_le_add (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le) le_rfl)
  simpa only [lowAdditionProgressionWeight,Int.cast_natCast,Int.cast_neg,neg_mul,sub_eq_add_neg] using hfinal

end JointDickman

end OAI
