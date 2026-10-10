import OAI.Analysis.SeparableQuotients.PathLimits

namespace OAI

noncomputable section

namespace SeparableQuotient.RealCoefficients
open Filter
open scoped Topology
universe u v
variable {ι : Type u} [Fintype ι]
variable {Z : Type v} [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Rational coefficients suffice for the closed finite-dimensional ℓq ball.
This uses actual density, not an assumed real Type II operation. -/
lemma rational_to_real (q : ℝ) (hq : 0 < q) (v : ι → Z)
    (h : ∀ c : ι → ℚ, (∑ i, |(c i : ℝ)| ^ q) ≤ 1 → ‖∑ i, (c i : ℝ) • v i‖ ≤ 1)
    (c : ι → ℝ) (hc : (∑ i, |c i| ^ q) ≤ 1) : ‖∑ i, c i • v i‖ ≤ 1 := by
  let Q : (ι → ℝ) → ℝ := fun c => ∑ i, |c i| ^ q
  let F : (ι → ℝ) → Z := fun c => ∑ i, c i • v i
  have hQ : Continuous Q := by
    apply continuous_finsetSum
    intro i _
    exact (Real.continuous_rpow_const hq.le).comp (continuous_apply i).abs
  have hF : Continuous F := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_apply i).smul continuous_const
  have hD : DenseRange (fun a : ι → ℚ => fun i => (a i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hstrict : ∀ a : ι → ℝ, Q a < 1 → ‖F a‖ ≤ 1 := by
    intro a ha
    have hclosed : IsClosed {a : ι → ℝ | ‖F a‖ ≤ 1} := isClosed_le hF.norm continuous_const
    apply closure_minimal (s := {a : ι → ℝ | Q a < 1} ∩
        Set.range (fun a : ι → ℚ => fun i => (a i : ℝ))) (t := {a | ‖F a‖ ≤ 1})
        (by rintro _ ⟨hb, b, rfl⟩; exact h b hb.le) hclosed
    exact hD.open_subset_closure_inter (isOpen_lt hQ continuous_const) ha
  let t : ℕ → ℝ := fun n => 1 - 1/((n+2 : ℕ) : ℝ)
  have ht0 (n : ℕ) : 0 ≤ t n := by
    dsimp [t]
    have hd : (1 : ℝ) ≤ ((n+2 : ℕ) : ℝ) := by norm_cast; omega
    have : 1/((n+2 : ℕ) : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hd
    linarith
  have ht1 (n : ℕ) : t n < 1 := by
    dsimp [t]
    have : 0 < 1/((n+2 : ℕ) : ℝ) := by positivity
    linarith
  have ht : Tendsto t atTop (𝓝 1) := by
    have hz : Tendsto (fun n : ℕ => 1/((n+2 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 2).mpr tendsto_one_div_atTop_nhds_zero_nat
    simpa only [sub_zero] using tendsto_const_nhds.sub hz
  have hb (n : ℕ) : ‖F (t n • c)‖ ≤ 1 := by
    apply hstrict
    have he : Q (t n • c) = (t n)^q * Q c := by
      dsimp only [Q]
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (ht0 n),
        Real.mul_rpow (ht0 n) (abs_nonneg _), Finset.mul_sum]
    rw [he]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (Real.rpow_nonneg (ht0 n) _) hc)
      (Real.rpow_lt_one (ht0 n) (ht1 n) hq)
  have htF : Tendsto (fun n => F (t n • c)) atTop (𝓝 (F c)) := by
    have hcT : Tendsto (fun n => t n • c) atTop (𝓝 c) := by
      simpa only [one_smul] using ht.smul (tendsto_const_nhds (x := c))
    exact (hF.tendsto c).comp hcT
  exact le_of_tendsto htF.norm (Eventually.of_forall hb)

end SeparableQuotient.RealCoefficients

namespace SeparableQuotient.RealCoefficients
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι]
variable {Z : Type v} [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma bound_from_unit (q : ℝ) (hq : 0 < q) (v : ι → Z)
    (h : ∀ c : ι → ℝ, (∑ i, |c i| ^ q) ≤ 1 → ‖∑ i, c i • v i‖ ≤ 1)
    (c : ι → ℝ) : ‖∑ i, c i • v i‖ ≤ (∑ i, |c i| ^ q) ^ (1/q) := by
  let z : ℝ := ∑ i, |c i| ^ q
  have hz : 0 ≤ z := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
  by_cases hz0 : z = 0
  · have hc0 (i : ι) : c i = 0 := by
      have hi : |c i| ^ q ≤ z := Finset.single_le_sum
        (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)
      rw [hz0] at hi
      have he : |c i| ^ q = 0 := le_antisymm hi (Real.rpow_nonneg (abs_nonneg _) _)
      exact abs_eq_zero.mp ((Real.rpow_eq_zero (abs_nonneg _) hq.ne').mp he)
    rw [show (∑ i, c i • v i) = 0 by simp [hc0], norm_zero]
    exact Real.rpow_nonneg hz _
  · let A : ℝ := z ^ (1/q)
    have hA : 0 < A := Real.rpow_pos_of_pos (lt_of_le_of_ne hz (Ne.symm hz0)) _
    have hAq : A^q = z := by
      rw [← Real.rpow_mul hz, one_div_mul_cancel hq.ne', Real.rpow_one]
    have hd : (∑ i, |c i/A| ^ q) = 1 := by
      simp only [abs_div, abs_of_pos hA, Real.div_rpow (abs_nonneg _) hA.le,
        ← Finset.sum_div, hAq]
      exact div_self hz0
    have hb := h (fun i => c i/A) hd.le
    have he : (∑ i, c i • v i) = A • (∑ i, (c i/A) • v i) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, mul_div_cancel₀ _ hA.ne']
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hA]
    exact mul_le_of_le_one_right hA.le hb

end SeparableQuotient.RealCoefficients

namespace SeparableQuotient.RealCoefficients

def signChoice (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

lemma abs_signChoice (x : ℝ) : |signChoice x| = 1 := by
  unfold signChoice
  split_ifs <;> norm_num

lemma signChoice_mul (x : ℝ) : signChoice x * x = |x| := by
  unfold signChoice
  split_ifs with h
  · simp only [one_mul, abs_of_nonneg h]
  · simp only [neg_one_mul, abs_of_neg (lt_of_not_ge h)]

end SeparableQuotient.RealCoefficients

end

end OAI
