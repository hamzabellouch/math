import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptronFreeEnergy

section Positivity

variable {Ω : Type*} [MeasurableSpace Ω]

abbrev OverlapBlock (n : ℕ) := Fin n → Fin n → ℝ

def overlapBlock (R : Ω → ℕ → ℕ → ℝ) (n : ℕ) (ω : Ω) : OverlapBlock n :=
  fun i j => R ω i j

def GhirlandaGuerra (μ : Measure Ω) (R : Ω → ℕ → ℕ → ℝ) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (i : Fin n) (s : Set (OverlapBlock n)), MeasurableSet s →
    ∀ t : Set ℝ, MeasurableSet t →
    μ.real ((overlapBlock R n) ⁻¹' s ∩ {ω | R ω i n ∈ t}) =
      μ.real ((overlapBlock R n) ⁻¹' s) * μ.real {ω | R ω 0 1 ∈ t} / n +
      (∑ j ∈ (Finset.univ.erase i),
        μ.real ((overlapBlock R n) ⁻¹' s ∩ {ω | R ω i j ∈ t})) / n

def negativeMatrices (n : ℕ) (δ : ℝ) : Set (OverlapBlock n) :=
  {q | ∀ i j : Fin n, i < j → q i j < -δ}

def negativeClique (R : Ω → ℕ → ℕ → ℝ) (n : ℕ) (δ : ℝ) : Set Ω :=
  (overlapBlock R n) ⁻¹' negativeMatrices n δ

lemma negativeMatrices_measurable (n : ℕ) (δ : ℝ) :
    MeasurableSet (negativeMatrices n δ) := by
  unfold negativeMatrices
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _h
  exact measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply i)) measurable_const

lemma overlapBlock_measurable {R : Ω → ℕ → ℕ → ℝ}
    (hR : ∀ i j, Measurable (fun ω => R ω i j)) (n : ℕ) :
    Measurable (overlapBlock R n) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact hR i j

lemma negativeClique_measurable {R : Ω → ℕ → ℕ → ℝ}
    (hR : ∀ i j, Measurable (fun ω => R ω i j)) (n : ℕ) (δ : ℝ) :
    MeasurableSet (negativeClique R n δ) :=
  (negativeMatrices_measurable n δ).preimage (overlapBlock_measurable hR n)

omit [MeasurableSpace Ω] in
lemma mem_negativeClique {R : Ω → ℕ → ℕ → ℝ} {n : ℕ} {δ : ℝ} {ω : Ω} :
    ω ∈ negativeClique R n δ ↔ ∀ i j : Fin n, i < j → R ω i j < -δ := Iff.rfl

omit [MeasurableSpace Ω] in
lemma negativeClique_succ (R : Ω → ℕ → ℕ → ℝ) (n : ℕ) (δ : ℝ) :
    negativeClique R (n + 1) δ = negativeClique R n δ ∩
      ⋂ i : Fin n, {ω | R ω i n < -δ} := by
  ext ω
  simp only [mem_inter_iff, mem_iInter, mem_ofPred]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact h i.castSucc j.castSucc (by exact hij)
    · intro i
      exact h i.castSucc (Fin.last n) (by simp)
  · rintro ⟨hold, hnew⟩ i j hij
    by_cases hj : j.val < n
    · exact hold ⟨i, lt_trans hij hj⟩ ⟨j, hj⟩ hij
    · have jeq : (j : ℕ) = n := by omega
      have hi : (i : ℕ) < n := by omega
      simpa only [overlapBlock, jeq] using hnew ⟨i, hi⟩

omit [MeasurableSpace Ω] in
lemma negativeClique_two (R : Ω → ℕ → ℕ → ℝ) (δ : ℝ) :
    negativeClique R 2 δ = {ω | R ω 0 1 < -δ} := by
  ext ω
  constructor
  · intro h
    exact h 0 1 (by decide)
  · intro h i j hij
    have hi : (i : ℕ) = 0 := by omega
    have hj : (j : ℕ) = 1 := by omega
    change R ω 0 1 < -δ at h
    simpa only [overlapBlock, hi, hj] using h

lemma measureReal_inter_iInter_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {E : Set Ω} {T : ι → Set Ω}
    (hT : ∀ i, MeasurableSet (T i)) :
    μ.real E - ∑ i, μ.real (E \ T i) ≤ μ.real (E ∩ ⋂ i, T i) := by
  classical
  have hu : E \ (⋂ i, T i) = ⋃ i ∈ (Finset.univ : Finset ι), E \ T i := by
    ext ω
    simp
  have hbound : μ.real (E \ ⋂ i, T i) ≤ ∑ i, μ.real (E \ T i) := by
    rw [hu]
    exact measureReal_biUnion_finset_le _ _
  have hsum := measureReal_inter_add_sdiff (μ := μ) (s := E) (MeasurableSet.iInter hT)
  linarith

lemma gg_negativeClique_extension (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℕ → ℝ} (hR : ∀ i j, Measurable (fun ω => R ω i j))
    (hsym : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hGG : GhirlandaGuerra μ R) {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) :
    μ.real {ω | R ω 0 1 < -δ} * μ.real (negativeClique R n δ) ≤
      μ.real (negativeClique R (n + 1) δ) := by
  classical
  let b := μ.real {ω | R ω 0 1 < -δ}
  let p := μ.real (negativeClique R n δ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htail (i : Fin n) :
      μ.real (negativeClique R n δ ∩ {ω | R ω i n < -δ}) = p * (b + (n - 1)) / n := by
    have h := hGG n hn i (negativeMatrices n δ) (negativeMatrices_measurable n δ)
      (Iio (-δ)) measurableSet_Iio
    have hpair (j : Fin n) (hji : j ≠ i) :
      μ.real (negativeClique R n δ ∩ {ω | R ω i j < -δ}) = p := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [hsym] with ω hω
      apply propext
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        change R ω i j < -δ
        rcases lt_or_gt_of_ne (Ne.symm hji) with hij | hij
        · exact h i j hij
        · rw [hω i j]
          exact h j i hij
    change μ.real (negativeClique R n δ ∩ {ω | R ω i n < -δ}) =
      p * b / n + (∑ j ∈ Finset.univ.erase i,
        μ.real (negativeClique R n δ ∩ {ω | R ω i j < -δ})) / n at h
    rw [Finset.sum_congr rfl (fun j hj => hpair j (Finset.ne_of_mem_erase hj))] at h
    have hcard : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      rw [Nat.cast_sub (by omega)]
      norm_num
    simp only [Finset.sum_const, nsmul_eq_mul, hcard] at h
    rw [h]
    ring
  have hbad (i : Fin n) :
      μ.real (negativeClique R n δ \ {ω | R ω i n < -δ}) = p * (1 - b) / n := by
    have h := measureReal_inter_add_sdiff (μ := μ) (s := negativeClique R n δ)
      (t := {ω | R ω i n < -δ}) (measurableSet_lt (hR i n) measurable_const)
    rw [htail i] at h
    change _ + _ = p at h
    apply (eq_div_iff (ne_of_gt hnpos)).mpr
    field_simp at h
    nlinarith
  rw [negativeClique_succ]
  have h := measureReal_inter_iInter_lower μ (E := negativeClique R n δ)
    (T := fun i : Fin n => {ω | R ω i n < -δ})
    (fun i => measurableSet_lt (hR i n) measurable_const)
  simp_rw [hbad] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have he : p - (n : ℝ) * (p * (1 - b) / n) = b * p := by
    field_simp
    ring
  rwa [he] at h

lemma negative_gram_sum_bound {n : ℕ} {Q : Fin n → Fin n → ℝ} {δ : ℝ}
    (hsym : ∀ i j, Q i j = Q j i) (hdiag : ∀ i, Q i i ≤ 1)
    (hneg : ∀ i j, i < j → Q i j < -δ) :
    (∑ i, ∑ j, Q i j) ≤ (n : ℝ) * (1 - δ * ((n : ℝ) - 1)) := by
  classical
  have hrow (i : Fin n) : (∑ j, Q i j) ≤ 1 - δ * ((n : ℝ) - 1) := by
    have hpair (j : Fin n) (hji : j ≠ i) : Q i j ≤ -δ := by
      rcases lt_or_gt_of_ne (Ne.symm hji) with hij | hij
      · exact (hneg i j hij).le
      · rw [hsym i j]
        exact (hneg j i hij).le
    have hs : (∑ j ∈ Finset.univ.erase i, Q i j) ≤
        ∑ _j ∈ Finset.univ.erase i, -δ :=
      Finset.sum_le_sum fun j hj => hpair j (Finset.ne_of_mem_erase hj)
    have hc : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      rw [Nat.cast_sub (by have := i.isLt; omega)]
      norm_num
    simp only [Finset.sum_const, nsmul_eq_mul, hc] at hs
    have ht := Finset.sum_erase_add Finset.univ (Q i) (Finset.mem_univ i)
    nlinarith [hdiag i]
  calc
    _ ≤ ∑ _i : Fin n, (1 - δ * ((n : ℝ) - 1)) := Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp; ring

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

end SphericalPerceptronFreeEnergy
end

end OAI
