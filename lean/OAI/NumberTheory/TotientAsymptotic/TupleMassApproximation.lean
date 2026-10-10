import OAI.NumberTheory.TotientAsymptotic.LowerPrimeCutoff
import OAI.NumberTheory.TotientAsymptotic.MassUpper

namespace OAI

/-! Largest-prime summation over the actual finite tuple set, with all weights. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def weightedTupleCount (x : ℝ) (H : ℕ) (t : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ τ ∈ tupleFinset x H t, f ((ell τ.tail.d : ℝ)/τ.tail.d)

lemma weightedTupleCount_eq_fibers {x t : ℝ} {H : ℕ} (hPH : P H ≤ H)
    (f : ℝ → ℝ) :
    weightedTupleCount x H t f = ∑ ζ ∈ prefixDataFinset x H,
      f ((ell ζ.d : ℝ)/ζ.d)*((tupleFinset x H t).filter (fun τ => τ.tail=ζ)).card := by
  have hmap : ∀ τ ∈ tupleFinset x H t, τ.tail ∈ prefixDataFinset x H := by
    intro τ hτ
    exact mem_prefixDataFinset.mpr ((mem_tupleFinset hPH).mp hτ).2.2.1
  have he := Finset.sum_fiberwise_of_maps_to' hmap
    (fun ζ : PrefixDatum (R x H) => f ((ell ζ.d : ℝ)/ζ.d))
  rw [weightedTupleCount, ← he]
  apply Finset.sum_congr rfl
  intro ζ _
  simp [mul_comm]

/-- Relative error in largest-prime summation, uniformly over all bounded
weights and all endpoints in a fixed interval `[a*x,x]`. -/
theorem weighted_tuple_mass_relative (hpnt : PrimeNumberTheoremInput)
    {a : ℝ} (ha : 0 < a) {H : ℕ} (hPH : P H < H) (hP : 1 ≤ P H)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, a*x ≤ t → t ≤ x →
      ∀ f : ℝ → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      |weightedTupleCount x H t f-(t/Real.log x)*M x H f| ≤
        ε*(t/Real.log x)*M x H (fun _ => 1) := by
  filter_upwards [shifted_prime_uniform_asymptotic hpnt ha hε,
    basic_prefix_denominator_log_small hPH hP, eventually_gt_atTop (1 : ℝ)] with x hp hs hx
  intro t ht htx f hf
  have ht0 : 0 < t := (mul_pos ha (zero_lt_one.trans hx)).trans_le ht
  rw [weightedTupleCount_eq_fibers hPH.le, mass_eq_sum_prefixData, mass_eq_sum_prefixData,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro ζ hζ
  have hz := mem_prefixDataFinset.mp hζ
  rw [tuple_fiber_eq_shiftedPrimeSet hPH.le ht0.le hz]
  have hD := basic_prefix_denominator_pos hPH.le hz
  have hc := hp (prefixDenominator ζ) hD (hs ζ hz) t ht htx
  have hD0 : (prefixDenominator ζ : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hden : (ζ.d : ℝ)*∏ i, (ζ.primes i-1 : ℕ) = prefixDenominator ζ := by
    simp only [prefixDenominator, Nat.cast_mul, Nat.cast_prod]
  rw [hden]
  have he : f ((ell ζ.d : ℝ)/ζ.d)*(↑(shiftedPrimeSet x t (prefixDenominator ζ)).card : ℝ)-
      t/Real.log x*(f ((ell ζ.d : ℝ)/ζ.d)/(prefixDenominator ζ : ℝ)) =
      f ((ell ζ.d : ℝ)/ζ.d)*((↑(shiftedPrimeSet x t (prefixDenominator ζ)).card : ℝ)-
        t/((prefixDenominator ζ : ℝ)*Real.log x)) := by ring
  rw [he, abs_mul, abs_of_nonneg (hf _).1]
  calc
    _ ≤ f ((ell ζ.d : ℝ)/ζ.d)*(ε*(t/((prefixDenominator ζ : ℝ)*Real.log x))) :=
      mul_le_mul_of_nonneg_left hc (hf _).1
    _ ≤ ε*(t/((prefixDenominator ζ : ℝ)*Real.log x)) :=
      mul_le_of_le_one_left
        (mul_nonneg hε.le (div_nonneg ht0.le (mul_nonneg
          (Nat.cast_nonneg _) (Real.log_pos hx).le))) (hf _).2
    _ = _ := by field_simp

lemma weightedTupleCount_one (x t : ℝ) (H : ℕ) :
    weightedTupleCount x H t (fun _ => 1) = (tupleFinset x H t).card := by
  simp [weightedTupleCount]

end TotientAsymptotic

end

end OAI
