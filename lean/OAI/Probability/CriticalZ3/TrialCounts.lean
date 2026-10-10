import OAI.Probability.CriticalZ3.ConditionalQuality

namespace OAI

universe uI uOmega

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

open MeasureTheory ProbabilityTheory Classical
namespace ShellEstimates
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Averaging disjoint blocking events supplies a deterministic shell layer. -/
theorem exists_layer {I : Type uI} [Fintype I] [Nonempty I]
    (Q A : I → Set Ω) (hAm : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (fun i j => Disjoint (A i) (A j))) {α : ℝ} (hα : 0 < α)
    (hblock : ∀ i, α*μ.real (Q i) ≤ μ.real (A i)) :
    ∃ i, μ.real (Q i) ≤ 1/(α*Fintype.card I) := by
  have hs : ∑ i, μ.real (A i) ≤ 1 := by
    rw [←measureReal_iUnion_fintype hAd hAm]
    exact measureReal_le_one
  have hsQ : α*(∑ i, μ.real (Q i)) ≤ 1 := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum (fun i _ => hblock i)).trans hs
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  by_contra! hnone
  have ht : (∑ _i : I, 1/(α*Fintype.card I)) < ∑ i, μ.real (Q i) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hnone i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ht
  have he : (Fintype.card I : ℝ)*(1/(α*Fintype.card I)) = 1/α := by field_simp
  rw [he] at ht
  have hh := (div_lt_iff₀ hα).mp ht
  nlinarith

theorem success_count_bound (S : Ω → ℝ) (hS : MemLp S 2 μ)
    {a : ℝ} (ha : 0 < a) (hmean : ∫ ω, S ω ∂μ = a)
    (hvar : variance S μ ≤ a) :
    μ.real {ω | S ω < a/2} ≤ 4/a := by
  have hcheb := meas_ge_le_variance_div_sq hS (show 0 < a/2 by positivity)
  rw [hmean] at hcheb
  have hs : {ω | S ω < a/2} ⊆ {ω | a/2 ≤ |S ω-a|} := by
    intro ω hω
    have hh : a/2 ≤ a-S ω := by dsimp at hω ⊢; linarith
    exact hh.trans (le_abs_self _ |>.trans_eq (abs_sub_comm a (S ω)))
  have hle : μ {ω | S ω < a/2} ≤ ENNReal.ofReal (variance S μ/(a/2)^2) :=
    (measure_mono hs).trans hcheb
  have hv0 : 0 ≤ variance S μ/(a/2)^2 := div_nonneg (variance_nonneg _ _) (sq_nonneg _)
  have hr : μ.real {ω | S ω < a/2} ≤ variance S μ/(a/2)^2 := by
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hle |>.trans_eq
      (ENNReal.toReal_ofReal hv0)
  apply hr.trans
  apply (div_le_iff₀ (sq_pos_of_pos (show 0 < a/2 by positivity))).mpr
  have he : (4/a)*(a/2)^2 = a := by field_simp; ring
  rwa [he]

/- Bad successes only need a first moment; no mutual independence is used. -/
omit [IsProbabilityMeasure μ] in
theorem bad_count_bound (Z : Ω → ℝ) (hZ : Integrable Z μ) (hZ0 : ∀ ω, 0 ≤ Z ω)
    {a γ τ : ℝ} (ha : 0 < a) (_hτ : 0 < τ)
    (hmean : ∫ ω, Z ω ∂μ ≤ a*γ/τ) :
    μ.real {ω | a/2 ≤ Z ω} ≤ 2*γ/τ := by
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hZ0) hZ (a/2)
  have hm : (a/2)*μ.real {ω | a/2 ≤ Z ω} ≤ a*γ/τ := h.trans hmean
  have he : (a/2)*(2*γ/τ) = a*γ/τ := by ring
  rw [←he] at hm
  exact (mul_le_mul_iff_right₀ (show 0 < a/2 by positivity)).mp hm

/- If there is no good success, either successes fall below half their mean
or at least half their mean are bad. This is purely deterministic. -/
omit [MeasurableSpace Ω] in
theorem no_good_subset (S Z : Ω → ℝ) (G : Set Ω) (a : ℝ)
    (h : ∀ ω, ω ∉ G → S ω ≤ Z ω) :
    Gᶜ ⊆ {ω | S ω < a/2} ∪ {ω | a/2 ≤ Z ω} := by
  intro ω hω
  by_cases hs : S ω < a/2
  · exact Or.inl hs
  · exact Or.inr (le_trans (le_of_not_gt hs) (h ω hω))

end ShellEstimates

namespace TrialCounts
open MeasureTheory ProbabilityTheory Classical
variable {Ω : Type uOmega} {I : Type uI} [MeasurableSpace Ω] [Fintype I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def count (A : I → Set Ω) : Ω → ℝ :=
  fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω

theorem count_memLp (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    MemLp (count A) 2 μ := by
  apply memLp_finsetSum
  intro i _
  exact (memLp_const (1 : ℝ)).indicator (hA i)

omit [MeasurableSpace Ω] in
theorem count_nonneg (A : I → Set Ω) (ω : Ω) : 0 ≤ count A ω := by
  apply Finset.sum_nonneg
  intro i _
  by_cases h : ω ∈ A i <;> simp [Set.indicator,h]

omit [IsProbabilityMeasure μ] in
theorem indicator_mean (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real A :=
  integral_indicator_one hA

theorem count_mean (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    (∫ ω, count A ω ∂μ) = ∑ i, μ.real (A i) := by
  unfold count
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_indicator_one (hA i)
  · intro i _
    exact ((memLp_const (1 : ℝ)).indicator (hA i)).integrable (by norm_num : (1 : ENNReal) ≤ 2)

omit [MeasurableSpace Ω] in
theorem indicator_product (A B : Set Ω) :
    A.indicator (fun _ => (1 : ℝ)) * B.indicator (fun _ => (1 : ℝ)) =
      (A ∩ B).indicator (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [Set.indicator,hA,hB]

/-- Pairwise independence is all that the success-count step needs. -/
theorem count_variance_le (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    {c : ℝ} (hc : ∀ i, μ.real (A i) = c)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ c*c) :
    variance (count A) μ ≤ Fintype.card I*c := by
  let X (i : I) : Ω → ℝ := (A i).indicator (fun _ => (1 : ℝ))
  have hX (i : I) : MemLp (X i) 2 μ := (memLp_const (1 : ℝ)).indicator (hA i)
  have hcov (i j : I) : covariance (X i) (X j) μ ≤ if i = j then c else 0 := by
    have hprod : X i * X j = (A i ∩ A j).indicator (fun _ => (1 : ℝ)) :=
      indicator_product (A i) (A j)
    rw [covariance_eq_sub (hX i) (hX j),hprod,
      indicator_mean μ _ ((hA i).inter (hA j))]
    change μ.real (A i ∩ A j) -
      (∫ ω, (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ)*
      (∫ ω, (A j).indicator (fun _ => (1 : ℝ)) ω ∂μ) ≤ _
    rw [indicator_mean μ _ (hA i),indicator_mean μ _ (hA j),hc i,hc j]
    by_cases hij : i = j
    · subst j
      simp only [ite_true,Set.inter_self,hc]
      nlinarith [sq_nonneg c]
    · simp only [hij,ite_false]
      linarith [hpair i j hij]
  have he : count A = ∑ i, X i := by ext ω; simp [count,X]
  rw [he,variance_sum hX]
  calc
    _ ≤ ∑ i : I, ∑ j : I, if i = j then c else 0 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov i j))
    _ = Fintype.card I*c := by simp

/-- No independence is required among bad successes or their quality tests. -/
theorem no_good_probability (A B : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    {c γ τ : ℝ} (hcpos : 0 < Fintype.card I*c) (hτ : 0 < τ)
    (hc : ∀ i, μ.real (A i) = c)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ c*c)
    (hbad : ∀ i, μ.real (B i) ≤ c*γ/τ) :
    μ.real {ω | ∀ i, ω ∈ A i → ω ∈ B i} ≤ 4/(Fintype.card I*c)+2*γ/τ := by
  let a : ℝ := Fintype.card I*c
  have hm : (∫ ω, count A ω ∂μ) = a := by
    rw [count_mean μ A hA]
    simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,a]
  have hs := ShellEstimates.success_count_bound μ (count A) (count_memLp μ A hA)
    hcpos hm (count_variance_le μ A hA hc hpair)
  have hbmean : (∫ ω, count B ω ∂μ) ≤ a*γ/τ := by
    rw [count_mean μ B hB]
    calc
      _ ≤ ∑ _i : I, c*γ/τ := Finset.sum_le_sum (fun i _ => hbad i)
      _ = a*γ/τ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,a]; ring
  have hb := ShellEstimates.bad_count_bound μ (count B)
    ((count_memLp μ B hB).integrable (by norm_num)) (count_nonneg B) hcpos hτ hbmean
  have hsub : {ω | ∀ i, ω ∈ A i → ω ∈ B i} ⊆
      {ω | count A ω < a/2} ∪ {ω | a/2 ≤ count B ω} := by
    intro ω hω
    by_cases hs : count A ω < a/2
    · exact Or.inl hs
    · apply Or.inr
      apply (le_of_not_gt hs).trans
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : ω ∈ A i
      · simp [Set.indicator,hi,hω i hi]
      · simp only [Set.indicator,hi,ite_false]
        split_ifs <;> norm_num
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add hs hb))

end TrialCounts

end OAI
