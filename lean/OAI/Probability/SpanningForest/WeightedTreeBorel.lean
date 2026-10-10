import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.WeightedTree

abbrev Field := (ℕ × ℕ) → ℝ

def weight (h : Field) (T : Finset (ℕ × ℕ)) : ℝ :=
  Real.exp (∑ p ∈ T, h p)

def partition (K : FiniteSubgraphCode) (h : Field) : ℝ :=
  ∑ T ∈ spanningTrees K, weight h T

def numerator (K : FiniteSubgraphCode) (e : ℕ × ℕ) (h : Field) : ℝ := by
  classical
  exact ∑ T ∈ (spanningTrees K).filter (fun T => e ∈ T), weight h T

def inclusion (K : FiniteSubgraphCode) (e : ℕ × ℕ) (h : Field) : ℝ :=
  numerator K e h / partition K h

theorem weight_pos (h : Field) (T : Finset (ℕ × ℕ)) :
    0 < weight h T := Real.exp_pos _

theorem partition_nonneg (K : FiniteSubgraphCode) (h : Field) :
    0 ≤ partition K h :=
  Finset.sum_nonneg (fun T _ => (weight_pos h T).le)

theorem partition_pos {K : FiniteSubgraphCode}
    (hK : (spanningTrees K).Nonempty) (h : Field) :
    0 < partition K h :=
  Finset.sum_pos (fun T _ => weight_pos h T) hK

theorem numerator_nonneg (K : FiniteSubgraphCode) (e : ℕ × ℕ) (h : Field) :
    0 ≤ numerator K e h := by
  classical
  exact Finset.sum_nonneg (fun T _ => (weight_pos h T).le)

theorem numerator_le_partition (K : FiniteSubgraphCode) (e : ℕ × ℕ) (h : Field) :
    numerator K e h ≤ partition K h := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun T _ _ => (weight_pos h T).le)

theorem inclusion_mem_Icc (K : FiniteSubgraphCode) (e : ℕ × ℕ) (h : Field) :
    inclusion K e h ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (numerator_nonneg K e h) (partition_nonneg K h), ?_⟩
  by_cases hzero : partition K h = 0
  · simp [inclusion, hzero]
  · exact (div_le_one (lt_of_le_of_ne (partition_nonneg K h) (Ne.symm hzero))).mpr
      (numerator_le_partition K e h)

theorem measurable_weight (T : Finset (ℕ × ℕ)) :
    Measurable (fun h : Field => weight h T) := by
  exact (Finset.measurable_sum T (fun p _ => measurable_pi_apply p)).exp

theorem measurable_partition (K : FiniteSubgraphCode) :
    Measurable (partition K) := by
  exact Finset.measurable_sum (spanningTrees K) (fun T _ => measurable_weight T)

theorem measurable_numerator (K : FiniteSubgraphCode) (e : ℕ × ℕ) :
    Measurable (numerator K e) := by
  classical
  exact Finset.measurable_sum _ (fun T _ => measurable_weight T)

theorem measurable_inclusion (K : FiniteSubgraphCode) (e : ℕ × ℕ) :
    Measurable (inclusion K e) :=
  (measurable_numerator K e).div (measurable_partition K)

theorem measurable_partition_joint :
    Measurable (fun q : FiniteSubgraphCode × Field => partition q.1 q.2) :=
  measurable_from_prod_countable_right measurable_partition

theorem measurable_inclusion_joint :
    Measurable (fun q : (FiniteSubgraphCode × (ℕ × ℕ)) × Field =>
      inclusion q.1.1 q.1.2 q.2) :=
  measurable_from_prod_countable_right (fun q => measurable_inclusion q.1 q.2)

def finiteField (S : Finset (ℕ × ℕ)) (t : ℝ) (y : Field) : Field :=
  fun p => if p ∈ S then y p - t / 2 else 0

theorem measurable_finiteField (S : Finset (ℕ × ℕ)) :
    Measurable (fun q : ℝ × Field => finiteField S q.1 q.2) := by
  apply Measurable.of_eval
  intro p
  by_cases hp : p ∈ S
  · have ht : Measurable (fun q : ℝ × Field => q.1 / (2 : ℝ)) :=
      measurable_fst.div_const (2 : ℝ)
    have hy : Measurable (fun q : ℝ × Field => q.2 p) :=
      (measurable_pi_apply p).comp measurable_snd
    simpa only [finiteField, ite_eq_left hp] using hy.fun_sub ht
  · simpa only [finiteField, ite_eq_right hp] using
      (measurable_const : Measurable (fun _ : ℝ × Field => (0 : ℝ)))

theorem measurable_finiteField_joint :
    Measurable (fun q : Finset (ℕ × ℕ) × (ℝ × Field) =>
      finiteField q.1 q.2.1 q.2.2) :=
  measurable_from_prod_countable_right measurable_finiteField

theorem measurable_finiteTilt_joint :
    Measurable
      (fun q : (FiniteSubgraphCode × ((ℕ × ℕ) × Finset (ℕ × ℕ))) × (ℝ × Field) =>
        inclusion q.1.1 q.1.2.1 (finiteField q.1.2.2 q.2.1 q.2.2)) := by
  apply measurable_from_prod_countable_right
  intro q
  exact (measurable_inclusion q.1 q.2.1).comp (measurable_finiteField q.2.2)

def extendField (y : EdgeCode → ℝ) : Field :=
  fun p => if hp : p.1 < p.2 then y ⟨p, hp⟩ else 0

@[simp] theorem extendField_apply (y : EdgeCode → ℝ) (e : EdgeCode) :
    extendField y e.1 = y e := by
  simp only [extendField, dite_eq_left e.2]

theorem measurable_extendField : Measurable extendField := by
  apply Measurable.of_eval
  intro p
  by_cases hp : p.1 < p.2
  · simpa only [extendField, dite_eq_left hp] using
      (measurable_pi_apply (⟨p, hp⟩ : EdgeCode))
  · simpa only [extendField, dite_eq_right hp] using
      (measurable_const : Measurable (fun _ : EdgeCode → ℝ => (0 : ℝ)))

theorem measurable_edgeFiniteTilt_joint :
    Measurable
      (fun q : (FiniteSubgraphCode × (EdgeCode × Finset (ℕ × ℕ))) ×
          (ℝ × (EdgeCode → ℝ)) =>
        inclusion q.1.1 q.1.2.1.1
          (finiteField q.1.2.2 q.2.1 (extendField q.2.2))) := by
  apply measurable_from_prod_countable_right
  intro q
  exact (measurable_inclusion q.1 q.2.1.1).comp
    ((measurable_finiteField q.2.2).comp
      (measurable_fst.prodMk (measurable_extendField.comp measurable_snd)))

theorem inclusion_zero_field (K : FiniteSubgraphCode) (e : ℕ × ℕ) :
    inclusion K e 0 =
      (((spanningTrees K).filter (fun T => e ∈ T)).card : ℝ) /
        ((spanningTrees K).card : ℝ) := by
  classical
  simp [inclusion, numerator, partition, weight]

theorem inclusion_zero_field_eq_ustCylinder (K : FiniteSubgraphCode) (e : EdgeCode) :
    inclusion K e.1 0 = (ustCylinder K {e} ∅).toReal := by
  classical
  rw [inclusion_zero_field]
  simp [ustCylinder, ENNReal.toReal_div]

theorem ofReal_inclusion_zero_field (K : FiniteSubgraphCode) (e : EdgeCode) :
    ENNReal.ofReal (inclusion K e.1 0) = ustCylinder K {e} ∅ := by
  classical
  by_cases hzero : (spanningTrees K).card = 0
  · have hempty : spanningTrees K = ∅ := Finset.card_eq_zero.mp hzero
    simp [inclusion, numerator, partition, ustCylinder, hempty]
  · rw [inclusion_zero_field,
      ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
    simp [ustCylinder]

theorem inclusion_eq_zero_of_not_mem {K : FiniteSubgraphCode} {e : ℕ × ℕ}
    (he : e ∉ K.2) (h : Field) : inclusion K e h = 0 := by
  classical
  have hfilter : (spanningTrees K).filter (fun T => e ∈ T) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro T hT
    obtain ⟨hT, heT⟩ := Finset.mem_filter.mp hT
    have hsub : T ⊆ K.2 := (Finset.mem_filter.mp hT).2.1
    exact he (hsub heT)
  simp [inclusion, numerator, hfilter]

theorem weight_image (T : Finset (ℕ × ℕ)) (φ : (ℕ × ℕ) → (ℕ × ℕ))
    (a b : Field) (hinj : Set.InjOn φ (T : Set (ℕ × ℕ)))
    (hfield : ∀ p ∈ T, b (φ p) = a p) :
    weight b (T.image φ) = weight a T := by
  classical
  unfold weight
  congr 1
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl hfield
  · intro p hp q hq hpq
    exact hinj hp hq hpq

end Problem336.WeightedTree

end

end OAI
