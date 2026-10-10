import OAI.Combinatorics.BalancedRyser.Probability.CountingExposurePosterior
import OAI.Combinatorics.BalancedRyser.Probability.CoverCountingExposure
import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformTower

namespace OAI

namespace Balanced.DeletionCountingExposure

noncomputable section
open scoped BigOperators
open CountingExposurePosterior InjectionExposureLaw
attribute [local instance] Classical.propDecidable

variable {G ι α : Type*} [Fintype G] [Fintype ι] [Fintype α]
  [DecidableEq G] [DecidableEq ι] [DecidableEq α]

def observation (P : Finset (G × ι))
    (ω : Experiment (G := G) (ι := ι) (α := α)) : P → (G × ι) × α :=
  fun j => (ω.1 j, ω.2 (ω.1 j).1 (ω.1 j).2)

theorem mem_countingHistory_iff_observation_eq (P : Finset (G × ι))
    (ω τ : Experiment (G := G) (ι := ι) (α := α)) :
    ω ∈ countingHistory P τ.1 τ.2 ↔ observation P ω = observation P τ := by
  constructor
  · intro h
    obtain ⟨hp, ho⟩ := (Finset.mem_filter.mp h).2
    funext j
    have ht : ω.1 j = τ.1 j := by
      simpa [permutationHistory] using
        (show ∀ t ∈ P, ω.1 t = τ.1 t from by simpa [permutationHistory] using hp) j j.property
    have hj : (τ.1 j).2 ∈ exposedIndices (P.map τ.1.toEmbedding) (τ.1 j).1 := by
      simp only [exposedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.mem_map.mpr ⟨j, j.property, rfl⟩
    have hv := (mem_history _ _ _).mp (ho (τ.1 j).1) (τ.1 j).2 hj
    simp only [observation, ht]
    exact Prod.ext rfl hv
  · intro h
    have ht (j : G × ι) (hj : j ∈ P) : ω.1 j = τ.1 j :=
      congrArg Prod.fst (congrFun h ⟨j, hj⟩)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa [permutationHistory] using ht
    · intro d
      apply (mem_history _ _ _).mpr
      intro j hj
      have hm : (d, j) ∈ P.map τ.1.toEmbedding := by
        simpa [exposedIndices] using hj
      obtain ⟨t, htP, he⟩ := Finset.mem_map.mp hm
      have hv := congrArg Prod.snd (congrFun h ⟨t, htP⟩)
      change ω.2 (ω.1 t).1 (ω.1 t).2 = τ.2 (τ.1 t).1 (τ.1 t).2 at hv
      rw [ht t htP] at hv
      change τ.1 t = (d, j) at he
      simpa [he] using hv

theorem fiberMean_eq_history (P : Finset (G × ι))
    (g : Experiment (G := G) (ι := ι) (α := α) → ℝ)
    (τ : Experiment (G := G) (ι := ι) (α := α)) :
    FiniteUniformTower.fiberMean (observation P) g (observation P τ) =
      𝔼 ω ∈ countingHistory P τ.1 τ.2, g ω := by
  classical
  let : DecidablePred (fun ω : Experiment (G := G) (ι := ι) (α := α) =>
      observation P ω = observation P τ) := fun _ => Classical.propDecidable _
  rw [expect_subtype (countingHistory P τ.1 τ.2) g]
  unfold FiniteUniformTower.fiberMean
  rw [← Fintype.expect_eq_sum_div_card]
  apply Fintype.expect_equiv
    (Equiv.subtypeEquivRight (fun ω =>
      (mem_countingHistory_iff_observation_eq P ω τ).symm))
  intro ω
  rfl

theorem expect_history_tower (P : Finset (G × ι))
    (g : Experiment (G := G) (ι := ι) (α := α) → ℝ) :
    (𝔼 τ : Experiment (G := G) (ι := ι) (α := α),
      𝔼 ω ∈ countingHistory P τ.1 τ.2, g ω) =
      𝔼 ω : Experiment (G := G) (ι := ι) (α := α), g ω := by
  simp_rw [← fiberMean_eq_history]
  simpa only [FiniteUniformTower.average, Fintype.expect_eq_sum_div_card] using
    FiniteUniformTower.average_fiberMean (observation P) g

theorem nextLine_eq_of_history (P : Finset (G × ι))
    (ω τ : Experiment (G := G) (ι := ι) (α := α))
    (h : ω ∈ countingHistory P τ.1 τ.2) (j : G × ι) (hj : j ∈ P) :
    nextLine ω j = nextLine τ j := by
  have he := congrFun ((mem_countingHistory_iff_observation_eq P ω τ).mp h) ⟨j, hj⟩
  exact congrArg (fun x : (G × ι) × α => (x.1.1, x.2)) he

def exposedLines (P : Finset (G × ι))
    (ω : Experiment (G := G) (ι := ι) (α := α)) : Finset (G × α) :=
  P.image (nextLine ω)

theorem exposedLines_eq_of_history (J P : Finset (G × ι)) (hJP : J ⊆ P)
    (ω τ : Experiment (G := G) (ι := ι) (α := α))
    (h : ω ∈ countingHistory P τ.1 τ.2) : exposedLines J ω = exposedLines J τ := by
  apply Finset.image_congr
  intro j hj
  exact nextLine_eq_of_history P ω τ h j (hJP hj)

section Affine
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}

def pastUncovered (C : Finset (Line F)) (P : Finset (Direction F × Fin k))
    (ω : Experiment (G := Direction F) (ι := Fin k) (α := F)) : Finset (Point F) :=
  uncoveredBy (exposedLines P ω ∪ C)

theorem pastUncovered_eq_of_history (C : Finset (Line F))
    (J P : Finset (Direction F × Fin k)) (hJP : J ⊆ P)
    (ω τ : Experiment (G := Direction F) (ι := Fin k) (α := F))
    (h : ω ∈ countingHistory P τ.1 τ.2) :
    pastUncovered C J ω = pastUncovered C J τ := by
  rw [pastUncovered, pastUncovered, exposedLines_eq_of_history J P hJP ω τ h]

theorem earlier_deletion_mark_iff (C : Finset (Line F))
    (J P : Finset (Direction F × Fin k)) (hJP : J ⊆ P)
    (j : Direction F × Fin k) (hj : j ∈ P)
    (ω τ : Experiment (G := Direction F) (ι := Fin k) (α := F))
    (h : ω ∈ countingHistory P τ.1 τ.2) (ε : ℝ) :
    CoverCountingExposure.Marked (pastUncovered C J ω) ε (nextLine ω j) ↔
      CoverCountingExposure.Marked (pastUncovered C J τ) ε (nextLine τ j) := by
  rw [pastUncovered_eq_of_history C J P hJP ω τ h,
    nextLine_eq_of_history P ω τ h j hj]

theorem earlier_cover_mark_iff (C : Finset (Line F))
    (J P : Finset (Direction F × Fin k)) (hJP : J ⊆ P) (l : Line F)
    (ω τ : Experiment (G := Direction F) (ι := Fin k) (α := F))
    (h : ω ∈ countingHistory P τ.1 τ.2) (ε : ℝ) :
    CoverCountingExposure.Marked (pastUncovered C J ω) ε l ↔
      CoverCountingExposure.Marked (pastUncovered C J τ) ε l := by
  rw [pastUncovered_eq_of_history C J P hJP ω τ h]

def priorMixedMarks {δ κ : Type*} (sD : Finset δ) (sC : Finset κ)
    (pastD₁ : δ → Finset (Direction F × Fin k)) (pastC₁ : δ → Finset (Line F))
    (positionD : δ → Direction F × Fin k)
    (pastD₂ : κ → Finset (Direction F × Fin k)) (pastC₂ : κ → Finset (Line F))
    (targetC : κ → Line F) (ε : ℝ)
    (ω : Experiment (G := Direction F) (ι := Fin k) (α := F)) : Prop :=
  (∀ j ∈ sD, CoverCountingExposure.Marked
    (pastUncovered (pastC₁ j) (pastD₁ j) ω) ε (nextLine ω (positionD j))) ∧
  ∀ j ∈ sC, CoverCountingExposure.Marked
    (pastUncovered (pastC₂ j) (pastD₂ j) ω) ε (targetC j)

theorem priorMixedMarks_iff_of_history {δ κ : Type*}
    (sD : Finset δ) (sC : Finset κ)
    (pastD₁ : δ → Finset (Direction F × Fin k)) (pastC₁ : δ → Finset (Line F))
    (positionD : δ → Direction F × Fin k)
    (pastD₂ : κ → Finset (Direction F × Fin k)) (pastC₂ : κ → Finset (Line F))
    (targetC : κ → Line F) (P : Finset (Direction F × Fin k))
    (hD : ∀ j ∈ sD, pastD₁ j ⊆ P ∧ positionD j ∈ P)
    (hC : ∀ j ∈ sC, pastD₂ j ⊆ P)
    (ω τ : Experiment (G := Direction F) (ι := Fin k) (α := F))
    (h : ω ∈ countingHistory P τ.1 τ.2) (ε : ℝ) :
    priorMixedMarks sD sC pastD₁ pastC₁ positionD pastD₂ pastC₂ targetC ε ω ↔
      priorMixedMarks sD sC pastD₁ pastC₁ positionD pastD₂ pastC₂ targetC ε τ := by
  unfold priorMixedMarks
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · intro j hj
      exact (earlier_deletion_mark_iff _ _ P (hD j hj).1 _ (hD j hj).2 ω τ h ε).mp
        (h₁ j hj)
    · intro j hj
      exact (earlier_cover_mark_iff _ _ P (hC j hj) _ ω τ h ε).mp (h₂ j hj)
  · rintro ⟨h₁, h₂⟩
    constructor
    · intro j hj
      exact (earlier_deletion_mark_iff _ _ P (hD j hj).1 _ (hD j hj).2 ω τ h ε).mpr
        (h₁ j hj)
    · intro j hj
      exact (earlier_cover_mark_iff _ _ P (hC j hj) _ ω τ h ε).mpr (h₂ j hj)

omit [Field F] in

theorem sum_remainingTokens_eq (P : Finset (Direction F × Fin k))
    (π : Equiv.Perm (Direction F × Fin k)) :
    (∑ d, (remainingTokens (P.map π.toEmbedding) d : ℝ)) =
      ((k * (Fintype.card F + 1) - P.card : ℕ) : ℝ) := by
  rw [sum_remainingTokens, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Finset.card_map]
  simp [Direction, Nat.mul_comm]

theorem marked_iff (U : Finset (Point F)) (ε : ℝ) (l : Line F) :
    CoverCountingExposure.Marked U ε l ↔ l ∈ CountingExposureKernel.markedLines U ε := by
  simp [CoverCountingExposure.Marked, CountingExposureKernel.markedLines]

theorem conditional_event_and_mark_le
    (P : Finset (Direction F × Fin k)) (i : Direction F × Fin k) (hi : i ∉ P)
    (A : Experiment (G := Direction F) (ι := Fin k) (α := F) → Prop)
    (U : Experiment (G := Direction F) (ι := Fin k) (α := F) → Finset (Point F))
    (hA : ∀ ω τ, ω ∈ countingHistory P τ.1 τ.2 → (A ω ↔ A τ))
    (hU : ∀ ω τ, ω ∈ countingHistory P τ.1 τ.2 → U ω = U τ)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (hk : 0 < k)
    (hqk : 2 * k ≤ Fintype.card F)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ((k * (Fintype.card F + 1) - P.card : ℕ) : ℝ))
    (τ : Experiment (G := Direction F) (ι := Fin k) (α := F)) :
    (𝔼 ω ∈ countingHistory P τ.1 τ.2,
      if A ω ∧ CoverCountingExposure.Marked (U ω) ε (nextLine ω i)
        then (1 : ℝ) else 0) ≤
      ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) * (if A τ then (1 : ℝ) else 0) := by
  have heq :
      (𝔼 ω ∈ countingHistory P τ.1 τ.2,
        if A ω ∧ CoverCountingExposure.Marked (U ω) ε (nextLine ω i)
          then (1 : ℝ) else 0) =
      (𝔼 ω ∈ countingHistory P τ.1 τ.2,
        if A τ ∧ CoverCountingExposure.Marked (U τ) ε (nextLine ω i)
          then (1 : ℝ) else 0) := by
    apply Finset.expect_congr rfl
    intro ω hω
    simp only [hA ω τ hω, hU ω τ hω]
  rw [heq]
  by_cases h : A τ
  · simp only [h, true_and, ite_true, mul_one]
    simp_rw [marked_iff]
    apply marked_probability_given_history_le P τ.1 τ.2 i hi (U τ) ε η hε hη hk hqk
    rwa [sum_remainingTokens_eq]
  · simp [h]

theorem past_event_and_mark_le
    (P : Finset (Direction F × Fin k)) (i : Direction F × Fin k) (hi : i ∉ P)
    (A : Experiment (G := Direction F) (ι := Fin k) (α := F) → Prop)
    (U : Experiment (G := Direction F) (ι := Fin k) (α := F) → Finset (Point F))
    (hA : ∀ ω τ, ω ∈ countingHistory P τ.1 τ.2 → (A ω ↔ A τ))
    (hU : ∀ ω τ, ω ∈ countingHistory P τ.1 τ.2 → U ω = U τ)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (hk : 0 < k)
    (hqk : 2 * k ≤ Fintype.card F)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ((k * (Fintype.card F + 1) - P.card : ℕ) : ℝ)) :
    (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
      if A ω ∧ CoverCountingExposure.Marked (U ω) ε (nextLine ω i)
        then (1 : ℝ) else 0) ≤
      ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) *
        (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
          if A ω then (1 : ℝ) else 0) := by
  rw [← expect_history_tower P]
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro τ _
  exact conditional_event_and_mark_le P i hi A U hA hU ε η hε hη hk hqk hremaining τ

theorem past_event_and_actual_mark_le
    (C : Finset (Line F)) (P : Finset (Direction F × Fin k))
    (i : Direction F × Fin k) (hi : i ∉ P)
    (A : Experiment (G := Direction F) (ι := Fin k) (α := F) → Prop)
    (hA : ∀ ω τ, ω ∈ countingHistory P τ.1 τ.2 → (A ω ↔ A τ))
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (hk : 0 < k)
    (hqk : 2 * k ≤ Fintype.card F)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ((k * (Fintype.card F + 1) - P.card : ℕ) : ℝ)) :
    (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
      if A ω ∧ CoverCountingExposure.Marked (pastUncovered C P ω) ε (nextLine ω i)
        then (1 : ℝ) else 0) ≤
      ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) *
        (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
          if A ω then (1 : ℝ) else 0) :=
  past_event_and_mark_le P i hi A (pastUncovered C P) hA
    (pastUncovered_eq_of_history C P P (Finset.Subset.refl P))
    ε η hε hη hk hqk hremaining

theorem prior_mixed_marks_and_actual_mark_le {δ κ : Type*}
    (sD : Finset δ) (sC : Finset κ)
    (pastD₁ : δ → Finset (Direction F × Fin k)) (pastC₁ : δ → Finset (Line F))
    (positionD : δ → Direction F × Fin k)
    (pastD₂ : κ → Finset (Direction F × Fin k)) (pastC₂ : κ → Finset (Line F))
    (targetC : κ → Line F) (C : Finset (Line F)) (P : Finset (Direction F × Fin k))
    (hD : ∀ j ∈ sD, pastD₁ j ⊆ P ∧ positionD j ∈ P)
    (hC : ∀ j ∈ sC, pastD₂ j ⊆ P)
    (i : Direction F × Fin k) (hi : i ∉ P)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (hk : 0 < k)
    (hqk : 2 * k ≤ Fintype.card F)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ((k * (Fintype.card F + 1) - P.card : ℕ) : ℝ)) :
    let A := priorMixedMarks sD sC pastD₁ pastC₁ positionD pastD₂ pastC₂ targetC ε
    (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
      if A ω ∧ CoverCountingExposure.Marked (pastUncovered C P ω) ε (nextLine ω i)
        then (1 : ℝ) else 0) ≤
      ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) *
        (𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
          if A ω then (1 : ℝ) else 0) := by
  apply past_event_and_actual_mark_le C P i hi _ _ ε η hε hη hk hqk hremaining
  intro ω τ h
  exact priorMixedMarks_iff_of_history sD sC pastD₁ pastC₁ positionD pastD₂ pastC₂
    targetC P hD hC ω τ h ε

theorem independent_outer_past_event_and_actual_mark_le {Ω : Type*} [Fintype Ω]
    (C : Ω → Finset (Line F)) (P : Finset (Direction F × Fin k))
    (i : Direction F × Fin k) (hi : i ∉ P)
    (A : Ω → Experiment (G := Direction F) (ι := Fin k) (α := F) → Prop)
    (hA : ∀ ζ ω τ, ω ∈ countingHistory P τ.1 τ.2 → (A ζ ω ↔ A ζ τ))
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (hk : 0 < k)
    (hqk : 2 * k ≤ Fintype.card F)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ((k * (Fintype.card F + 1) - P.card : ℕ) : ℝ)) :
    (𝔼 ζ : Ω, 𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
      if A ζ ω ∧ CoverCountingExposure.Marked (pastUncovered (C ζ) P ω) ε (nextLine ω i)
        then (1 : ℝ) else 0) ≤
      ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) *
        (𝔼 ζ : Ω, 𝔼 ω : Experiment (G := Direction F) (ι := Fin k) (α := F),
          if A ζ ω then (1 : ℝ) else 0) := by
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro ζ _
  exact past_event_and_actual_mark_le (C ζ) P i hi (A ζ) (hA ζ)
    ε η hε hη hk hqk hremaining

end Affine
end
end Balanced.DeletionCountingExposure

end OAI
