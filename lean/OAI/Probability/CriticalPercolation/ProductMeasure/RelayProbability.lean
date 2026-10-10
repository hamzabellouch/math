import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.PredictionFailure

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation
variable {Ω : Type*} [MeasurableSpace Ω]

lemma relay_failure_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ℕ → Set Ω) (κ : ℝ) (N : ℕ)
    (h : ∀ i<N, μ.real (A i\A (i+1)) ≤ κ) :
    μ.real (A 0\A N) ≤ N*κ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsub : A 0\A (N+1) ⊆ (A 0\A N)∪(A N\A (N+1)) := by
      intro ω hω
      by_cases hn : ω∈A N
      · exact Or.inr ⟨hn,hω.2⟩
      · exact Or.inl ⟨hω.1,hn⟩
    calc
      _ ≤ μ.real ((A 0\A N)∪(A N\A (N+1))) := measureReal_mono hsub
      _ ≤ μ.real (A 0\A N)+μ.real (A N\A (N+1)) := measureReal_union_le _ _
      _ ≤ N*κ+κ := add_le_add (ih (fun i hi => h i (by omega))) (h N (by omega))
      _ = _ := by push_cast; ring

lemma relay_miss_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ℕ → Set Ω) (κ η : ℝ) (N : ℕ)
    (hfirst : μ.real (A 0)ᶜ ≤ η)
    (h : ∀ i<N, μ.real (A i\A (i+1)) ≤ κ) :
    μ.real (A N)ᶜ ≤ η+N*κ := by
  have hsub : (A N)ᶜ⊆(A 0)ᶜ∪(A 0\A N) := by
    intro ω hω
    by_cases h0 : ω∈A 0
    · exact Or.inr ⟨h0,hω⟩
    · exact Or.inl h0
  calc
    _ ≤ μ.real ((A 0)ᶜ∪(A 0\A N)) := measureReal_mono hsub
    _ ≤ μ.real (A 0)ᶜ+μ.real (A 0\A N) := measureReal_union_le _ _
    _ ≤ _ := add_le_add hfirst (relay_failure_bound μ A κ N h)

namespace BernoulliProduct
variable {E : Type*}

def twoPredictions (q : E → unitInterval) (S : Set E) (C D : Set (Set E))
    (δ : ℝ) : Set (Set E) :=
  {σ | 1-δ ≤ (blockProbability q S C σ).toReal ∧
    1-δ ≤ (blockProbability q S D σ).toReal}

lemma measurableSet_twoPredictions (q : E → unitInterval) (S : Set E)
    (C D : Set (Set E)) (hC : MeasurableSet C) (hD : MeasurableSet D) (δ : ℝ) :
    MeasurableSet[blockSigma S] (twoPredictions q S C D δ) :=
  (measurableSet_le measurable_const
    ((measurable_blockProbability q S C hC).ennreal_toReal)).inter
  (measurableSet_le measurable_const
    ((measurable_blockProbability q S D hD).ennreal_toReal))

theorem twoPredictions_positive (q : E → unitInterval) (S : Set E)
    (C D : Set (Set E)) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (δ a : ℝ) (hδ : 0<δ) (ha : 2*a<δ)
    (hc : (law q).real Cᶜ ≤ a) (hd : (law q).real Dᶜ ≤ a) :
    0<(law q).real (twoPredictions q S C D δ) := by
  have h1 := bad_prediction_bound q S Set.univ C MeasurableSet.univ hC δ hδ
  have h2 := bad_prediction_bound q S Set.univ D MeasurableSet.univ hD δ hδ
  have hcEq : Set.univ \ C = Cᶜ := by ext; simp
  have hdEq : Set.univ \ D = Dᶜ := by ext; simp
  simp only [Set.univ_inter,hcEq,hdEq] at h1 h2
  have he : (twoPredictions q S C D δ)ᶜ=
      {σ | (blockProbability q S C σ).toReal<1-δ}∪
      {σ | (blockProbability q S D σ).toReal<1-δ} := by
    ext σ
    simp only [twoPredictions,Set.mem_compl_iff,Set.mem_ofPred_eq,Set.mem_union,not_and_or,not_le]
  have hm := (blockSigma_le S) _ (measurableSet_twoPredictions q S C D hC hD δ)
  have hcomp : (law q).real (twoPredictions q S C D δ)ᶜ<1 := by
    rw [he]
    calc
      _ ≤ (law q).real {σ | (blockProbability q S C σ).toReal<1-δ}+
          (law q).real {σ | (blockProbability q S D σ).toReal<1-δ} := measureReal_union_le _ _
      _ ≤ (law q).real Cᶜ/δ+(law q).real Dᶜ/δ := add_le_add h1 h2
      _ ≤ a/δ+a/δ := add_le_add (div_le_div_of_nonneg_right hc hδ.le)
        (div_le_div_of_nonneg_right hd hδ.le)
      _ = 2*a/δ := by ring
      _ < 1 := (div_lt_one hδ).mpr ha
  rw [probReal_compl_eq_one_sub hm] at hcomp
  linarith

end BernoulliProduct
end CriticalPercolation
end
end
end

end OAI
