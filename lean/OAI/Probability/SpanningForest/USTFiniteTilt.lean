import OAI.Probability.SpanningForest.USTResponse

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.USTResponse

def observationField (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (t : ℝ) (y : (ℕ × ℕ) → ℝ) : FiniteEdge K → ℝ :=
  fun e => if e.1 ∈ S then y e.1 - t / 2 else 0

def finiteTilt (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (t : ℝ) (y : (ℕ × ℕ) → ℝ) (e : ℕ × ℕ) : ℝ :=
  if he : e ∈ K.2 then inclusion K (observationField K S t y) ⟨e, he⟩ else 0

lemma finiteTilt_of_mem (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (t : ℝ) (y : (ℕ × ℕ) → ℝ) (e : ℕ × ℕ) (he : e ∈ K.2) :
    finiteTilt K S t y e = inclusion K (observationField K S t y) ⟨e, he⟩ := by
  simp [finiteTilt, he]

lemma finiteTilt_of_not_mem (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (t : ℝ) (y : (ℕ × ℕ) → ℝ) (e : ℕ × ℕ) (he : e ∉ K.2) :
    finiteTilt K S t y e = 0 := by
  simp [finiteTilt, he]

lemma finiteTilt_mem_Icc (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (hne : (spanningTrees K).Nonempty)
    (t : ℝ) (y : (ℕ × ℕ) → ℝ) (e : ℕ × ℕ) :
    finiteTilt K S t y e ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases he : e ∈ K.2
  · rw [finiteTilt_of_mem K S t y e he]
    exact ⟨inclusion_nonneg K _ hne _, inclusion_le_one K _ hne _⟩
  · simp [finiteTilt_of_not_mem K S t y e he]

lemma continuous_observationField (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ)) :
    Continuous (fun q : ℝ × ((ℕ × ℕ) → ℝ) => observationField K S q.1 q.2) := by
  apply continuous_pi
  intro e
  unfold observationField
  split_ifs <;> fun_prop

lemma continuous_finiteTilt (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (hne : (spanningTrees K).Nonempty) (e : ℕ × ℕ) :
    Continuous (fun q : ℝ × ((ℕ × ℕ) → ℝ) => finiteTilt K S q.1 q.2 e) := by
  by_cases he : e ∈ K.2
  · simpa only [finiteTilt, dite_eq_left he, Function.comp_def] using
      (continuous_inclusion K hne ⟨e, he⟩).comp (continuous_observationField K S)
  · simp only [finiteTilt, dite_eq_right he]
    exact continuous_const

lemma measurable_finiteTilt (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (hne : (spanningTrees K).Nonempty) (e : ℕ × ℕ) :
    Measurable (fun q : ℝ × ((ℕ × ℕ) → ℝ) => finiteTilt K S q.1 q.2 e) :=
  (continuous_finiteTilt K S hne e).measurable

lemma finiteTilt_eq_zero_of_no_trees (K : FiniteSubgraphCode)
    (hempty : ¬ (spanningTrees K).Nonempty) (S : Finset (ℕ × ℕ))
    (t : ℝ) (y : (ℕ × ℕ) → ℝ) (e : ℕ × ℕ) :
    finiteTilt K S t y e = 0 := by
  let : IsEmpty (TreeSample K) := ⟨fun T => hempty ⟨T.1, T.2⟩⟩
  unfold finiteTilt
  split_ifs <;> simp [inclusion, FiniteResponse.mean]

lemma continuous_finiteTilt_unconditional (K : FiniteSubgraphCode)
    (S : Finset (ℕ × ℕ)) (e : ℕ × ℕ) :
    Continuous (fun q : ℝ × ((ℕ × ℕ) → ℝ) => finiteTilt K S q.1 q.2 e) := by
  by_cases hne : (spanningTrees K).Nonempty
  · exact continuous_finiteTilt K S hne e
  · simp only [finiteTilt_eq_zero_of_no_trees K hne]
    exact continuous_const

lemma measurable_finiteTilt_unconditional (K : FiniteSubgraphCode)
    (S : Finset (ℕ × ℕ)) (e : ℕ × ℕ) :
    Measurable (fun q : ℝ × ((ℕ × ℕ) → ℝ) => finiteTilt K S q.1 q.2 e) :=
  (continuous_finiteTilt_unconditional K S e).measurable

lemma measurable_finiteTilt_joint :
    Measurable (fun q : (FiniteSubgraphCode × (Finset (ℕ × ℕ) × (ℕ × ℕ))) ×
        (ℝ × ((ℕ × ℕ) → ℝ)) =>
      finiteTilt q.1.1 q.1.2.1 q.2.1 q.2.2 q.1.2.2) := by
  apply measurable_from_prod_countable_right
  intro p
  exact measurable_finiteTilt_unconditional p.1 p.2.1 p.2.2

theorem finiteTilt_response_of_response (K : FiniteSubgraphCode)
    (hresponse : ∀ (a b : FiniteEdge K → ℝ) (e : FiniteEdge K) (D : ℝ),
      0 ≤ D → (∀ f, |b f - a f| ≤ D) →
        |inclusion K b e - inclusion K a e| ≤ D / 2)
    (S : Finset (ℕ × ℕ)) (t : ℝ) (y y' : (ℕ × ℕ) → ℝ) (e : ℕ × ℕ)
    (D : ℝ) (hD : 0 ≤ D) (hy : ∀ f ∈ S, |y' f - y f| ≤ D) :
    |finiteTilt K S t y' e - finiteTilt K S t y e| ≤ D / 2 := by
  by_cases he : e ∈ K.2
  · rw [finiteTilt_of_mem K S t y' e he, finiteTilt_of_mem K S t y e he]
    apply hresponse _ _ _ D hD
    intro f
    by_cases hf : f.1 ∈ S
    · simpa only [observationField, ite_eq_left hf, sub_sub_sub_cancel_right] using hy f.1 hf
    · simpa only [observationField, ite_eq_right hf, sub_self, abs_zero] using hD
  · simp only [finiteTilt, dite_eq_right he, sub_self, abs_zero]
    exact div_nonneg hD (by norm_num)

theorem finiteTilt_response (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (hne : (spanningTrees K).Nonempty)
    (hneg : ∀ h e f, e ≠ f → edgeCovariance K h e f ≤ 0)
    (t : ℝ) (y y' : (ℕ × ℕ) → ℝ) (e : ℕ × ℕ)
    (D : ℝ) (hD : 0 ≤ D) (hy : ∀ f ∈ S, |y' f - y f| ≤ D) :
    |finiteTilt K S t y' e - finiteTilt K S t y e| ≤ D / 2 := by
  by_cases he : e ∈ K.2
  · rw [finiteTilt_of_mem K S t y' e he, finiteTilt_of_mem K S t y e he]
    apply inclusion_response_of_coordinate_bound K hne hneg _ _ _ D hD
    intro f
    by_cases hf : f.1 ∈ S
    · simpa only [observationField, ite_eq_left hf, sub_sub_sub_cancel_right] using hy f.1 hf
    · simpa only [observationField, ite_eq_right hf, sub_self, abs_zero] using hD
  · simp only [finiteTilt, dite_eq_right he, sub_self, abs_zero]
    exact div_nonneg hD (by norm_num)

lemma observationField_zero (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ)) :
    observationField K S 0 0 = 0 := by
  funext e
  simp [observationField]

lemma observationField_empty (K : FiniteSubgraphCode) (t : ℝ)
    (y : (ℕ × ℕ) → ℝ) : observationField K ∅ t y = 0 := by
  funext e
  simp [observationField]

lemma finiteTilt_empty_eq_zero_field (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (t : ℝ) (y : (ℕ × ℕ) → ℝ) (e : ℕ × ℕ) :
    finiteTilt K ∅ t y e = finiteTilt K S 0 0 e := by
  simp only [finiteTilt, observationField_empty, observationField_zero]

lemma finiteTilt_zero_eq_ustCylinder_of_mem (K : FiniteSubgraphCode)
    (S : Finset (ℕ × ℕ)) (e : EdgeCode) (he : e.1 ∈ K.2) :
    finiteTilt K S 0 0 e.1 = (ustCylinder K {e} ∅).toReal := by
  rw [finiteTilt_of_mem K S 0 0 e.1 he, observationField_zero,
    inclusion_zero_eq_ustCylinder K e he]

end Problem336.USTResponse

end

end OAI
