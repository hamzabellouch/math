import OAI.Analysis.FiniteFactor.CrossedProduct.Cocycle

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal
noncomputable section

/-- Crossing 1-fract(a) raises the integer floor by exactly one, for either
sign of a. The half-open endpoints match the source's representatives. -/
theorem floor_crossing_gap {x y a : ℝ} (hx : x ∈ Set.Ico 0 1) (hy : y ∈ Set.Ico 0 1)
    (hcross : x < 1-Int.fract a ∧ 1-Int.fract a ≤ y) :
    Int.floor (y+a) = Int.floor (x+a)+1 := by
  have he (t : ℝ) : t+a = (t+Int.fract a)+(Int.floor a : ℝ) := by rw [Int.fract]; ring
  have hxf : Int.floor (x+Int.fract a) = 0 :=
    Int.floor_eq_zero_iff.mpr ⟨add_nonneg hx.1 (Int.fract_nonneg _), by linarith [hcross.1]⟩
  have hyf : Int.floor (y+Int.fract a) = 1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · norm_num
      linarith [hcross.2]
    · norm_num
      linarith [hy.2, Int.fract_lt_one a]
  rw [he y, he x, Int.floor_add_intCast, Int.floor_add_intCast, hxf, hyf]
  omega

/-- Every actual threshold crossing supplies the factor exp(-c_i) in the
source cocycle ratio. No attenuation property of an operator is assumed. -/
theorem sourceCocycle_crossing_attenuation {ι : Type*} (θ c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) {x y : ι → ℝ}
    (hx : finiteFloorSupport θ x) (hy : finiteFloorSupport θ y)
    (hxy : ∀ i, x i ≤ y i) (k : ℤ) (i : ι)
    (hxi : x i ∈ Set.Ico 0 1) (hyi : y i ∈ Set.Ico 0 1)
    (hcross : x i < 1-Int.fract ((k : ℝ)*θ i) ∧ 1-Int.fract ((k : ℝ)*θ i) ≤ y i) :
    sourceCocycle θ c k y / sourceCocycle θ c k x ≤ Real.exp (-c i) := by
  have hs := (sourceLog_summable θ c hy k).sub (sourceLog_summable θ c hx k)
  have hnon (j : ι) : 0 ≤ c j * (coordinateFloor θ k y j : ℝ) - c j * (coordinateFloor θ k x j : ℝ) := by
    apply sub_nonneg.mpr
    apply mul_le_mul_of_nonneg_left _ (hc j)
    have hh : coordinateFloor θ k x j ≤ coordinateFloor θ k y j :=
      Int.floor_mono (add_le_add (hxy j) le_rfl)
    exact_mod_cast hh
  have hgap : c i * (coordinateFloor θ k y i : ℝ) - c i * (coordinateFloor θ k x i : ℝ) = c i := by
    have hh := floor_crossing_gap hxi hyi hcross
    change coordinateFloor θ k y i = coordinateFloor θ k x i + 1 at hh
    rw [hh, Int.cast_add, Int.cast_one]
    ring
  have hle := hs.le_tsum i (fun j _ => hnon j)
  rw [hgap, (sourceLog_summable θ c hy k).tsum_sub (sourceLog_summable θ c hx k)] at hle
  rw [sourceCocycle, sourceCocycle, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  change c i ≤ sourceLog θ c k y - sourceLog θ c k x at hle
  linarith

/-- The genuine finite-prefix bound for the source cocycle F_n. This is the
pointwise estimate needed before lifting the bound to powers of T. -/
theorem sourceCocycle_prefix_bound {ι : Type*} (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (hx0 : ∀ i, 0 ≤ x i) (I : Finset ι) (n : ℕ) :
    sourceCocycle θ c n x ≤ Real.exp ((∑ i ∈ I, c i) - (n : ℝ)*(∑ i ∈ I, c i*θ i)) := by
  have hnon (i : ι) : 0 ≤ c i * (coordinateFloor θ n x i : ℝ) := by
    apply mul_nonneg (hc i)
    have hi : 0 ≤ coordinateFloor θ n x i :=
      Int.floor_nonneg.mpr (add_nonneg (hx0 i) (mul_nonneg (by exact_mod_cast Nat.zero_le n) (hθ i)))
    exact_mod_cast hi
  have hlo (i : ι) : c i * ((n : ℝ)*θ i-1) ≤ c i * (coordinateFloor θ n x i : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (hc i)
    have hh := Int.lt_floor_add_one (x i + (n : ℝ)*θ i)
    change (n : ℝ)*θ i-1 ≤ (Int.floor (x i+(n : ℝ)*θ i) : ℝ)
    linarith [hx0 i]
  have hsum := (Finset.sum_le_sum (fun i (_hi : i ∈ I) => hlo i)).trans
    ((sourceLog_summable θ c hx n).sum_le_tsum I (fun i _ => hnon i))
  have he : (∑ i ∈ I, c i * ((n : ℝ)*θ i-1)) =
      (n : ℝ)*(∑ i ∈ I, c i*θ i) - ∑ i ∈ I, c i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hsum
  apply Real.exp_le_exp.mpr
  change _ ≤ sourceLog θ c n x at hsum
  linarith

end
end FiniteFactor

end OAI
