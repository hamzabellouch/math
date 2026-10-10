import Mathlib

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
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

end Positivity
end SphericalPerceptron
end
end

end OAI
