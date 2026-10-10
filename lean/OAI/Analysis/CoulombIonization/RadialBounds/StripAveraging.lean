import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CoulombRadialAveraging

def slidingBit (l r d t : ℝ) : ℝ := if d-r ≤ t ∧ t ≤ d+l then 1 else 0

def slidingCount {N : ℕ} (d : Fin N → ℝ) (l r t : ℝ) : ℝ :=
  ∑ i, slidingBit l r (d i) t

def upperCount {N : ℕ} (d : Fin N → ℝ) (R : ℝ) : ℝ :=
  ∑ i, if d i ≤ R then 1 else 0

lemma slidingBit_nonneg (l r d t : ℝ) : 0 ≤ slidingBit l r d t := by
  unfold slidingBit; split_ifs <;> norm_num

lemma slidingBit_le_one (l r d t : ℝ) : slidingBit l r d t ≤ 1 := by
  unfold slidingBit; split_ifs <;> norm_num

lemma slidingBit_measurable {α : Type*} [MeasurableSpace α]
    {d t : α → ℝ} (hd : Measurable d) (ht : Measurable t) (l r : ℝ) :
    Measurable (fun x => slidingBit l r (d x) (t x)) := by
  exact Measurable.ite ((measurableSet_le (hd.sub_const r) ht).inter
    (measurableSet_le ht (hd.add_const l))) measurable_const measurable_const

lemma slidingCount_nonneg {N : ℕ} (d : Fin N → ℝ) (l r t : ℝ) :
    0 ≤ slidingCount d l r t := Finset.sum_nonneg (fun _ _ => slidingBit_nonneg _ _ _ _)

lemma slidingCount_le {N : ℕ} (d : Fin N → ℝ) (l r t : ℝ) :
    slidingCount d l r t ≤ N := by
  calc
    _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum (fun _ _ => slidingBit_le_one _ _ _ _)
    _ = N := by simp

lemma upperCount_nonneg {N : ℕ} (d : Fin N → ℝ) (R : ℝ) :
    0 ≤ upperCount d R := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> norm_num

lemma upperCount_le {N : ℕ} (d : Fin N → ℝ) (R : ℝ) : upperCount d R ≤ N := by
  calc
    _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
    _ = N := by simp

lemma slidingCount_measurable {α : Type*} [MeasurableSpace α] {N : ℕ}
    {d : α → Fin N → ℝ} {t : α → ℝ}
    (hd : ∀ i, Measurable (fun x => d x i)) (ht : Measurable t) (l r : ℝ) :
    Measurable (fun x => slidingCount (d x) l r (t x)) :=
  Finset.measurable_sum _ (fun i _ => slidingBit_measurable (hd i) ht l r)

lemma upperCount_measurable {α : Type*} [MeasurableSpace α] {N : ℕ}
    {d : α → Fin N → ℝ} (hd : ∀ i, Measurable (fun x => d x i)) (R : ℝ) :
    Measurable (fun x => upperCount (d x) R) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_le (hd i) measurable_const) measurable_const measurable_const

lemma slidingCount_sq_integrable {α : Type*} [MeasurableSpace α] {N : ℕ}
    {d : α → Fin N → ℝ} {t : α → ℝ} {μ : Measure α} [IsFiniteMeasure μ]
    (hd : ∀ i, Measurable (fun x => d x i)) (ht : Measurable t) (l r : ℝ) :
    Integrable (fun x => slidingCount (d x) l r (t x)^2) μ := by
  apply Integrable.of_bound ((slidingCount_measurable hd ht l r).pow_const 2).aestronglyMeasurable
    ((N:ℝ)^2)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (slidingCount_nonneg _ _ _ _) (slidingCount_le _ _ _ _) 2)

lemma upperCount_sq_integrable {α : Type*} [MeasurableSpace α] {N : ℕ}
    {d : α → Fin N → ℝ} {μ : Measure α} [IsFiniteMeasure μ]
    (hd : ∀ i, Measurable (fun x => d x i)) (R : ℝ) :
    Integrable (fun x => upperCount (d x) R^2) μ := by
  apply Integrable.of_bound ((upperCount_measurable hd R).pow_const 2).aestronglyMeasurable
    ((N:ℝ)^2)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (upperCount_nonneg _ _) (upperCount_le _ _) 2)

lemma slidingBit_eq_indicator (l r d : ℝ) :
    slidingBit l r d = (Icc (d-r) (d+l)).indicator (fun _ => (1:ℝ)) := by
  funext t
  simp only [slidingBit,Set.indicator,mem_Icc]

lemma slidingBit_integrable (l r d : ℝ) : Integrable (slidingBit l r d) := by
  rw [slidingBit_eq_indicator]
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrable_const 1

lemma slidingBit_integral {l r : ℝ} (h : 0 ≤ l+r) (d : ℝ) :
    ∫ t, slidingBit l r d t = l+r := by
  rw [slidingBit_eq_indicator]
  rw [integral_indicator_const 1 measurableSet_Icc]
  simp only [Measure.real,Real.volume_Icc,smul_eq_mul,mul_one]
  rw [show d+l-(d-r)=l+r by ring,ENNReal.toReal_ofReal h]

lemma slidingBit_setIntegral_le {l r : ℝ} (h : 0 ≤ l+r) (d lo hi : ℝ) :
    ∫ t in Icc lo hi, slidingBit l r d t ≤ l+r := by
  rw [←slidingBit_integral h d]
  exact integral_mono_measure Measure.restrict_le_self
    (ae_of_all _ (slidingBit_nonneg l r d)) (slidingBit_integrable l r d)

lemma slidingCount_eq_sum_upper {N : ℕ} (d : Fin N → ℝ) (l r hi t : ℝ) (ht : t ≤ hi) :
    slidingCount d l r t = ∑ i ∈ Finset.univ.filter (fun i => d i ≤ hi+r),
      slidingBit l r (d i) t := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi'
  have hh : ¬ d i ≤ hi+r := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi'
  unfold slidingBit
  rw [ite_eq_right]
  intro h
  exact hh (by linarith [h.1])

lemma upperCount_eq_card {N : ℕ} (d : Fin N → ℝ) (R : ℝ) :
    upperCount d R = ((Finset.univ.filter (fun i => d i ≤ R)).card:ℝ) := by
  classical
  simp [upperCount,Finset.sum_boole]

theorem slidingCount_square_integral {N : ℕ} (d : Fin N → ℝ) (lo hi : ℝ)
    {l r : ℝ} (h : 0 ≤ l+r) :
    (∫ t in Icc lo hi, slidingCount d l r t^2) ≤
      (l+r)*upperCount d (hi+r)^2 := by
  classical
  let S := Finset.univ.filter (fun i => d i ≤ hi+r)
  have he (t : ℝ) (ht : t ∈ Icc lo hi) := slidingCount_eq_sum_upper d l r hi t ht.2
  have hs (t : ℝ) : (∑ i ∈ S, slidingBit l r (d i) t) ≤ (S.card:ℝ) := by
    simpa only [nsmul_eq_mul,mul_one] using
      Finset.sum_le_card_nsmul S (fun i => slidingBit l r (d i) t) 1
        (fun _ _ => slidingBit_le_one _ _ _ _)
  have hint : Integrable (fun t => (S.card:ℝ)*∑ i ∈ S, slidingBit l r (d i) t)
      (volume.restrict (Icc lo hi)) :=
    (integrable_finsetSum _ (fun i _ => (slidingBit_integrable l r (d i)).restrict)).const_mul _
  calc
    _ ≤ ∫ t in Icc lo hi, (S.card:ℝ)*∑ i ∈ S, slidingBit l r (d i) t := by
      apply integral_mono_ae
        (slidingCount_sq_integrable (d := fun _ : ℝ => d) (fun _ => measurable_const) measurable_id l r) hint
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      change slidingCount d l r t^2 ≤ _
      rw [he t ht]
      have hn := Finset.sum_nonneg (s := S) (fun i _ => slidingBit_nonneg l r (d i) t)
      have hh := mul_le_mul_of_nonneg_right (hs t) hn
      nlinarith
    _ = (S.card:ℝ)*∑ i ∈ S, ∫ t in Icc lo hi, slidingBit l r (d i) t := by
      rw [integral_const_mul,integral_finsetSum _
        (fun i _ => (slidingBit_integrable l r (d i)).restrict)]
    _ ≤ (S.card:ℝ)*∑ _i ∈ S, (l+r) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => slidingBit_setIntegral_le h (d i) lo hi)) (Nat.cast_nonneg _)
    _ = (l+r)*upperCount d (hi+r)^2 := by
      rw [upperCount_eq_card]
      simp only [Finset.sum_const,nsmul_eq_mul]
      dsimp only [S]
      ring

theorem expected_slidingCount_square_integral {α : Type*} [MeasurableSpace α]
    {N : ℕ} {d : α → Fin N → ℝ} (hd : ∀ i, Measurable (fun x => d x i))
    (μ : Measure α) [IsFiniteMeasure μ] (lo hi : ℝ) {l r : ℝ} (h : 0 ≤ l+r) :
    (∫ t in Icc lo hi, ∫ x, slidingCount (d x) l r t^2 ∂μ) ≤
      (l+r)*(∫ x, upperCount (d x) (hi+r)^2 ∂μ) := by
  have hp : Integrable (fun p : ℝ × α => slidingCount (d p.2) l r p.1^2)
      ((volume.restrict (Icc lo hi)).prod μ) :=
    slidingCount_sq_integrable (fun i => (hd i).comp measurable_snd) measurable_fst l r
  rw [integral_integral_swap hp,←integral_const_mul]
  apply integral_mono hp.integral_prod_right ((upperCount_sq_integrable hd (hi+r)).const_mul _)
  intro x
  exact slidingCount_square_integral (d x) lo hi h

theorem exists_radius_expected_square {α : Type*} [MeasurableSpace α]
    {N : ℕ} {d : α → Fin N → ℝ} (hd : ∀ i, Measurable (fun x => d x i))
    (μ : Measure α) [IsFiniteMeasure μ] {lo hi l r : ℝ}
    (hab : lo < hi) (h : 0 ≤ l+r) :
    ∃ t ∈ Icc lo hi, (∫ x, slidingCount (d x) l r t^2 ∂μ) ≤
      ((l+r)/(hi-lo))*(∫ x, upperCount (d x) (hi+r)^2 ∂μ) := by
  let ν := volume.restrict (Icc lo hi)
  have hνreal : ν.real univ = hi-lo := by
    simp only [ν,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_pos.mpr hab).le]
  have hν : ν ≠ 0 := by
    intro hh
    have hz : ν.real univ = 0 := by rw [hh]; simp
    rw [hνreal] at hz
    linarith
  have hp : Integrable (fun p : ℝ × α => slidingCount (d p.2) l r p.1^2) (ν.prod μ) :=
    slidingCount_sq_integrable (fun i => (hd i).comp measurable_snd) measurable_fst l r
  have hn : ν (Icc lo hi)ᶜ = 0 := by
    simp only [ν,Measure.restrict_apply measurableSet_Icc.compl,compl_inter_self,measure_empty]
  obtain ⟨t,ht,havg⟩ := exists_notMem_null_le_average hν hp.integral_prod_left hn
  refine ⟨t,not_not.mp ht,?_⟩
  rw [average_eq,hνreal,smul_eq_mul] at havg
  have hb := expected_slidingCount_square_integral hd μ lo hi h
  calc
    _ ≤ (hi-lo)⁻¹*(∫ t in Icc lo hi, ∫ x, slidingCount (d x) l r t^2 ∂μ) := havg
    _ ≤ (hi-lo)⁻¹*((l+r)*(∫ x, upperCount (d x) (hi+r)^2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (sub_pos.mpr hab).le)
    _ = _ := by ring

end CoulombRadialAveraging

end

end OAI
