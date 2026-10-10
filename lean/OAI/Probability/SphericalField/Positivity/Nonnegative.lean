import Mathlib
import OAI.Probability.SphericalField.Positivity.Cliques

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
section Positivity
variable {Ω : Type*} [MeasurableSpace Ω]
lemma negativeClique_null (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℕ → ℝ}
    (hsym : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, R ω i i ≤ 1)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂μ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, R ω i j)
    {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 1 < δ * ((n : ℝ) - 1)) :
    μ (negativeClique R n δ) = 0 := by
  have hnot : ∀ᵐ ω ∂μ, ω ∉ negativeClique R n δ := by
    filter_upwards [hsym, hdiag, hpos n] with ω hωs hωd hωp
    intro hωn
    have hb := negative_gram_sum_bound
      (Q := fun i j : Fin n => R ω i j)
      (fun i j => hωs i j) (fun i => hωd i) hωn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have : (n : ℝ) * (1 - δ * ((n : ℝ) - 1)) < 0 :=
      mul_neg_of_pos_of_neg hn' (by linarith)
    linarith
  simpa only [not_not, ofPred_mem_eq] using ae_iff.mp hnot

theorem gg_negative_threshold_null (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℕ → ℝ} (hR : ∀ i j, Measurable (fun ω => R ω i j))
    (hsym : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, R ω i i ≤ 1)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂μ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, R ω i j)
    (hGG : GhirlandaGuerra μ R) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | R ω 0 1 < -δ} = 0 := by
  apply (measureReal_eq_zero_iff (μ := μ)).mp
  apply le_antisymm _ measureReal_nonneg
  by_contra hb
  have hbpos : 0 < μ.real {ω | R ω 0 1 < -δ} := lt_of_not_ge hb
  have hcpos (k : ℕ) : 0 < μ.real (negativeClique R (k + 2) δ) := by
    induction k with
    | zero => simpa only [zero_add, negativeClique_two] using hbpos
    | succ k hk =>
      have he := gg_negativeClique_extension μ hR hsym hGG (n := k + 2) (by omega) δ
      exact (mul_pos hbpos hk).trans_le he
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / δ)
  have hkδ : 1 < (k : ℝ) * δ := (div_lt_iff₀ hδ).mp hk
  have he : 1 < δ * (((k + 2 : ℕ) : ℝ) - 1) := by
    push_cast
    nlinarith
  have hz := negativeClique_null μ hsym hdiag hpos (n := k + 2) (by omega) he
  have hz' : μ.real (negativeClique R (k + 2) δ) = 0 := (measureReal_eq_zero_iff (μ := μ)).mpr hz
  linarith [hcpos k]

theorem gg_overlap_nonnegative (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℕ → ℝ} (hR : ∀ i j, Measurable (fun ω => R ω i j))
    (hsym : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, R ω i i ≤ 1)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂μ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, R ω i j)
    (hGG : GhirlandaGuerra μ R) :
    ∀ᵐ ω ∂μ, 0 ≤ R ω 0 1 := by
  have ht (k : ℕ) : ∀ᵐ ω ∂μ, -(1 / ((k : ℝ) + 1)) ≤ R ω 0 1 := by
    rw [ae_iff]
    simpa only [not_le] using gg_negative_threshold_null μ hR hsym hdiag hpos hGG
      (δ := 1 / ((k : ℝ) + 1)) (by positivity)
  filter_upwards [ae_all_iff.mpr ht] with ω hω
  have hlim : Tendsto (fun k : ℕ => -(1 / ((k : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  exact le_of_tendsto hlim (Eventually.of_forall hω)

end Positivity

lemma gg_star_growth_impossible {a : ℕ → ℝ} {N ζ : ℝ}
    (hN : 2 ≤ N) (hζ : 0 < ζ) (ha : ∀ k, 0 ≤ a k) (hzero : 0 < a 0)
    (hrec : ∀ k, (N + k) * a (k + 1) = (N + k - 1 + ζ) * a k)
    (hbound : ∀ k : ℕ, (k + 1 : ℝ) * a k ≤ 1) : False := by
  let b : ℕ → ℝ := fun k => (N + k - 1) * a k
  have hbzero : 0 < b 0 := by dsimp [b]; nlinarith
  have hdiff (k : ℕ) : b (k + 1) = b k + ζ * a k := by
    dsimp [b]
    push_cast
    nlinarith [hrec k]
  have hbmono : Monotone b := monotone_nat_of_le_succ fun k => by
    rw [hdiff]
    exact le_add_of_nonneg_right (mul_nonneg hζ.le (ha k))
  have hblower (k : ℕ) : b 0 ≤ b k := hbmono (Nat.zero_le k)
  have hbupper (k : ℕ) : b k ≤ N := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc
      b k ≤ N * ((k + 1 : ℝ) * a k) := by
        dsimp [b]
        have : N + (k : ℝ) - 1 ≤ N * (k + 1) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this (ha k)]
      _ ≤ N := by nlinarith [hbound k]
  have hsum (k : ℕ) : ζ * ∑ j ∈ Finset.range k, a j = b k - b 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, mul_add, ih, hdiff]; ring
  have hasum : Summable a := by
    apply summable_of_sum_range_le ha (c := N / ζ)
    intro k
    apply (le_div_iff₀ hζ).mpr
    nlinarith [hsum k, hbupper k]
  have hdom (k : ℕ) : (1 / (k + 1 : ℝ)) ≤ (N / b 0) * a k := by
    have hk : (0 : ℝ) < k + 1 := by positivity
    rw [div_le_iff₀ hk]
    have : b 0 ≤ N * ((k + 1 : ℝ) * a k) := by
      calc b 0 ≤ b k := hblower k
           _ ≤ N * ((k + 1 : ℝ) * a k) := by
             dsimp [b]
             have hknonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
             have : N + (k : ℝ) - 1 ≤ N * (k + 1) := by nlinarith
             nlinarith [mul_le_mul_of_nonneg_right this (ha k)]
    have hn : N * ((k + 1 : ℝ) * a k) / b 0 ≥ 1 :=
      (le_div_iff₀ hbzero).mpr (by simpa using this)
    calc 1 ≤ N * ((k + 1 : ℝ) * a k) / b 0 := hn
         _ = (N / b 0) * a k * (k + 1 : ℝ) := by ring
  have hharm : Summable (fun k : ℕ => 1 / (k + 1 : ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hdom (hasum.mul_left (N / b 0))
  have hharm' : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hharm
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hharm')

end SphericalPerceptron
end
end

end OAI
