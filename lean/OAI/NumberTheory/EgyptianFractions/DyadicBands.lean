import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.DyadicBands

/-- A half-open band on a multiplicative dyadic scale. -/
def InBand (a : ℝ) (j : ℕ) (x : ℝ) : Prop :=
  a * 2 ^ j ≤ x ∧ x < a * 2 ^ (j + 1)

instance (a : ℝ) (j : ℕ) (x : ℝ) : Decidable (InBand a j x) := by
  unfold InBand
  infer_instance

/-- Number of dyadic bands needed to cover `[a,B]`. -/
def bandCount (a B : ℝ) : ℕ :=
  ⌊Real.log (B / a) / Real.log 2⌋₊ + 1

lemma exists_band {a B x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxB : x ≤ B) :
    ∃ j : ℕ, j < bandCount a B ∧ InBand a j x := by
  have hratio : 1 ≤ x / a := (le_div_iff₀ ha).2 (by simpa using hax)
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hjB : (2 : ℝ) ^ j ≤ B / a :=
    hjlo.trans (div_le_div_of_nonneg_right hxB ha.le)
  have hjlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ j) hjB
  rw [Real.log_pow] at hjlog
  have hjbound : (j : ℝ) ≤ Real.log (B / a) / Real.log 2 :=
    (le_div_iff₀ hlog2).2 hjlog
  refine ⟨j, ?_, ?_, ?_⟩
  · exact Nat.lt_succ_of_le (Nat.le_floor hjbound)
  · have h := (le_div_iff₀ ha).1 hjlo
    nlinarith
  · have h := (div_lt_iff₀ ha).1 hjhi
    nlinarith

lemma bandCount_le {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    (bandCount a B : ℝ) ≤ 1 + Real.log (B / a) / Real.log 2 := by
  have hquot : 1 ≤ B / a := (le_div_iff₀ ha).2 (by simpa using haB)
  have hlog : 0 ≤ Real.log (B / a) := Real.log_nonneg hquot
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf := Nat.floor_le (div_nonneg hlog hlog2.le)
  unfold bandCount
  push_cast
  linarith

/-- A uniform bound on the weight in each dyadic band bounds the total weight.
This only uses coverage, so it is applicable without any injectivity assumption
on the scale attached to each element. -/
theorem sum_le_bandCount_mul {ι : Type*} (s : Finset ι)
    (x w : ι → ℝ) {a B A : ℝ} (ha : 0 < a)
    (hrange : ∀ i ∈ s, a ≤ x i ∧ x i ≤ B)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hband : ∀ j < bandCount a B,
      (∑ i ∈ s with InBand a j (x i), w i) ≤ A) :
    (∑ i ∈ s, w i) ≤ (bandCount a B : ℝ) * A := by
  classical
  have hcover : ∀ i ∈ s, w i ≤
      ∑ j ∈ Finset.range (bandCount a B), if InBand a j (x i) then w i else 0 := by
    intro i hi
    obtain ⟨j, hj, hji⟩ := exists_band ha (hrange i hi).1 (hrange i hi).2
    have hh := Finset.single_le_sum
      (s := Finset.range (bandCount a B))
      (f := fun j => if InBand a j (x i) then w i else 0)
      (fun j hj => by split_ifs; exact hw i hi; exact le_rfl)
      (Finset.mem_range.mpr hj)
    simpa only [ite_eq_left hji] using hh
  calc
    (∑ i ∈ s, w i) ≤
        ∑ i ∈ s, ∑ j ∈ Finset.range (bandCount a B),
          if InBand a j (x i) then w i else 0 := Finset.sum_le_sum hcover
    _ = ∑ j ∈ Finset.range (bandCount a B),
        ∑ i ∈ s with InBand a j (x i), w i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_filter]
    _ ≤ ∑ _j ∈ Finset.range (bandCount a B), A := by
      apply Finset.sum_le_sum
      intro j hj
      exact hband j (Finset.mem_range.mp hj)
    _ = (bandCount a B : ℝ) * A := by simp

/-- Real-valued logarithmic budget for a dyadic partition. -/
theorem sum_le_log_budget {ι : Type*} (s : Finset ι)
    (x w : ι → ℝ) {a B A : ℝ} (ha : 0 < a) (haB : a ≤ B) (hA : 0 ≤ A)
    (hrange : ∀ i ∈ s, a ≤ x i ∧ x i ≤ B)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hband : ∀ j < bandCount a B,
      (∑ i ∈ s with InBand a j (x i), w i) ≤ A) :
    (∑ i ∈ s, w i) ≤ (1 + Real.log (B / a) / Real.log 2) * A := by
  exact (sum_le_bandCount_mul s x w ha hrange hw hband).trans
    (mul_le_mul_of_nonneg_right (bandCount_le ha haB) hA)

/-- If the entire scale lies below `S²`, only `O(log S)` bands are needed. -/
lemma bandCount_le_log {a B S : ℝ} (ha : 1 ≤ a) (haB : a ≤ B)
    (hS : 2 ≤ S) (hB : B ≤ S ^ 2) :
    (bandCount a B : ℝ) ≤ (3 / Real.log 2) * Real.log S := by
  have ha0 : 0 < a := by linarith
  have hB0 : 0 < B := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogS : Real.log 2 ≤ Real.log S := Real.log_le_log (by norm_num) hS
  have hquot : B / a ≤ S ^ 2 := by
    calc
      B / a ≤ B / 1 := div_le_div_of_nonneg_left hB0.le (by norm_num) ha
      _ ≤ S ^ 2 := by simpa using hB
  have hquot0 : 0 < B / a := div_pos hB0 ha0
  have hlog := Real.log_le_log hquot0 hquot
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlogdiv : Real.log (B / a) / Real.log 2 ≤
      (2 * Real.log S) / Real.log 2 :=
    div_le_div_of_nonneg_right hlog hlog2.le
  have hone : 1 ≤ Real.log S / Real.log 2 :=
    (le_div_iff₀ hlog2).2 (by simpa using hlogS)
  have hc := bandCount_le ha0 haB
  have hbudget : 1 + Real.log (B / a) / Real.log 2 ≤
      (3 / Real.log 2) * Real.log S := by
    simp only [div_eq_mul_inv] at hlogdiv hone ⊢
    nlinarith
  exact hc.trans hbudget

/-- The uniform intermediate-band contribution has logarithmic total loss. -/
theorem sum_le_logS_budget {ι : Type*} (s : Finset ι)
    (x w : ι → ℝ) {a B S A : ℝ}
    (ha : 1 ≤ a) (haB : a ≤ B) (hS : 2 ≤ S) (hB : B ≤ S ^ 2)
    (hA : 0 ≤ A) (hrange : ∀ i ∈ s, a ≤ x i ∧ x i ≤ B)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hband : ∀ j < bandCount a B,
      (∑ i ∈ s with InBand a j (x i), w i) ≤ A) :
    (∑ i ∈ s, w i) ≤ (3 / Real.log 2) * Real.log S * A := by
  exact (sum_le_bandCount_mul s x w (by linarith) hrange hw hband).trans
    (mul_le_mul_of_nonneg_right (bandCount_le_log ha haB hS hB) hA)

/-- The precise dyadic cover used for the intermediate-prime range in the
uniform divisor moment. The constant is absolute; the threshold depends on `D`. -/
theorem eventually_divisor_band_cover (D : ℝ) :
    ∀ᶠ S : ℝ in Filter.atTop, ∀ v : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      4 * Real.log S ≤ v ^ (15 / 16 : ℝ) →
      ∃ J : ℕ, (J : ℝ) ≤ (3 / Real.log 2) * Real.log S ∧
        ∀ w : ℝ, 4 * Real.log S ≤ w → w < v ^ (15 / 16 : ℝ) →
          ∃ j : ℕ, j < J ∧ InBand (4 * Real.log S) j w := by
  filter_upwards [Filter.eventually_ge_atTop (max D (Real.exp 4))] with S hS
  have hSD : D ≤ S := (le_max_left _ _).trans hS
  have hSe : Real.exp 4 ≤ S := (le_max_right _ _).trans hS
  have hSpos : 0 < S := (Real.exp_pos 4).trans_le hSe
  have hlog : 4 ≤ Real.log S := (Real.le_log_iff_exp_le hSpos).2 hSe
  have hS2 : 2 ≤ S := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hquad := Real.pow_div_factorial_le_exp (Real.log S) (by linarith) 2
  norm_num at hquad
  rw [Real.exp_log hSpos] at hquad
  have htwo : 2 * Real.log S ≤ S := by nlinarith
  have hlogpos : 0 < 2 * Real.log S := by positivity
  have hratio : 1 ≤ S / (2 * Real.log S) :=
    (le_div_iff₀ hlogpos).2 (by simpa using htwo)
  intro v hvlo hvhi haB
  have hv1 : 1 ≤ v := hratio.trans hvlo
  have hrpow : v ^ (15 / 16 : ℝ) ≤ v := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num : (15 / 16 : ℝ) ≤ 1)
  have hB : v ^ (15 / 16 : ℝ) ≤ S ^ 2 := by
    calc
      v ^ (15 / 16 : ℝ) ≤ v := hrpow
      _ ≤ D * S := hvhi
      _ ≤ S ^ 2 := by nlinarith
  refine ⟨bandCount (4 * Real.log S) (v ^ (15 / 16 : ℝ)),
    bandCount_le_log (by linarith) haB hS2 hB, ?_⟩
  intro w hwlo hwhi
  exact exists_band (by positivity) hwlo hwhi.le

end Problem337.DyadicBands

end

end OAI
