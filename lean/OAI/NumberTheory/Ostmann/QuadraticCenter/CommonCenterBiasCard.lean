import OAI.NumberTheory.Ostmann.QuadraticCenter.CommonCenterBiasBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem card_large_abs_of_mean {ι : Type*} (U : Finset ι) (f : ι → ℝ)
    (hU : 0 < U.card) {c : ℝ} (hc : 0≤c)
    (hf : ∀x∈U,|f x|≤1) (hmean : c≤|(∑x∈U,f x)/U.card|) :
    (c/2)*(U.card:ℝ)≤((U.filter (fun x => c/2≤|f x|)).card:ℝ) := by
  classical
  have hUp : (0:ℝ)<U.card := by exact_mod_cast hU
  rw [abs_div,abs_of_pos hUp] at hmean
  have hm := (le_div_iff₀ hUp).mp hmean
  have hb (x : ι) (hx : x∈U) :
      |f x|≤c/2+(if c/2≤|f x| then (1:ℝ) else 0) := by
    by_cases hh : c/2≤|f x|
    · rw [ite_eq_left hh]
      linarith [hf x hx]
    · rw [ite_eq_right hh]
      linarith
  have hsum : (∑x∈U,|f x|)≤(U.card:ℝ)*(c/2)+
      ((U.filter (fun x => c/2≤|f x|)).card:ℝ) := by
    calc
      _ ≤ ∑x∈U,(c/2+(if c/2≤|f x| then (1:ℝ) else 0)) := Finset.sum_le_sum hb
      _ = _ := by
        rw [Finset.sum_add_distrib,← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  have htri := Finset.abs_sum_le_sum_abs f U
  nlinarith

theorem affineKernelAverage_numerator_ne_zero (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    (ε : ℕ → ℤ) (m : ℕ) (h x : ℤ) {c : ℝ} (hc : 0 < c)
    (hx : c≤|affineKernelAverage P ε m h x|) : (m:ℤ)*x-h≠0 := by
  intro hz
  rw [affineKernelAverage_eq_zero P hP ε m h x hz,abs_zero] at hx
  linarith

end Ostmann.QuadraticCenter

end

end OAI
