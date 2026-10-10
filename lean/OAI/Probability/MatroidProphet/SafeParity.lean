import OAI.Probability.MatroidProphet.SafeSamples

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def safeEndpointParityCount (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (C T : Finset α) (parity : Bool) : ℝ :=
  ∑ i ∈ range (pathHorizon h-1), if safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T ∧
    (-(i:ℤ)) % 2 = (if parity then 1 else 0) then 1 else 0

noncomputable def safeSampleCount (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) (parity : Bool) : ℝ :=
  ∑ d ∈ I, safeEndpointParityCount M hE κ D G h d C T parity

omit [DecidableEq α] in
lemma safeSampleCount_parity_split (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) :
    safeSampleCount M hE κ D G h I C T false + safeSampleCount M hE κ D G h I C T true =
      safeCountBeforeParity M hE κ D G h I C T := by
  unfold safeSampleCount safeCountBeforeParity
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  unfold safeEndpointParityCount safeEndpointCount
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have hm0 := Int.emod_nonneg (-(i:ℤ)) (by norm_num : (2:ℤ) ≠ 0)
  have hm1 := Int.emod_lt_of_pos (-(i:ℤ)) (by norm_num : (0:ℤ) < 2)
  have hm : (-(i:ℤ)) % 2 = 0 ∨ (-(i:ℤ)) % 2 = 1 := by omega
  by_cases hs : safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T
  · rcases hm with hm | hm <;> simp [hs, hm]
  · simp [hs]

noncomputable def fairParityExpectation (f : Bool → ℝ) : ℝ := (f false + f true) / 2

omit [DecidableEq α] in
lemma safeSampleCount_fair_parity (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) :
    fairParityExpectation (safeSampleCount M hE κ D G h I C T) =
      safeCountBeforeParity M hE κ D G h I C T / 2 := by
  unfold fairParityExpectation
  rw [safeSampleCount_parity_split]

theorem safeSampleCount_lower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (I : Finset α) (hI : M.Indep (I : Set α)) :
    (((2:ℝ)^12)⁻¹) / 4 * I.card - (D h).ncard / (κ:ℝ) ≤
      bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (safeSampleCount M hE κ D G h I C T))) := by
  have hpre := safeCountBeforeParity_lower M hE κ hκ D G hG q hq0 hq1 h I hI
  have heq : bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
        fairParityExpectation (safeSampleCount M hE κ D G h I C T))) =
      (bitsExpectation q univ (fun C => bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C))) / 2 := by
    simp only [safeSampleCount_fair_parity, div_eq_mul_inv]
    rw [show bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      safeCountBeforeParity M hE κ D G h I C T * (2:ℝ)⁻¹)) =
        bitsExpectation q univ (fun C => bitsExpectation q univ (safeCountBeforeParity M hE κ D G h I C) * (2:ℝ)⁻¹) from by
          apply bitsExpectation_congr; intro C hC; exact bitsExpectation_mul_right q univ _ _]
    exact bitsExpectation_mul_right q univ _ _
  rw [heq]
  have hnonneg : 0 ≤ (D h).ncard / (κ:ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  linarith

omit [Fintype α] [DecidableEq α] in
lemma sum_unique_indicators {ι : Type*} (J : Finset ι) (p : ι → Prop) [DecidablePred p]
    (huniq : ∀ i ∈ J, ∀ j ∈ J, p i → p j → i = j) :
    (∑ i ∈ J, if p i then (1:ℝ) else 0) = if ∃ i ∈ J, p i then 1 else 0 := by
  classical
  by_cases hex : ∃ i ∈ J, p i
  · obtain ⟨i, hi, hp⟩ := hex
    rw [ite_eq_left ⟨i, hi, hp⟩]
    calc
      _ = if p i then (1:ℝ) else 0 := by
        apply sum_eq_single i
        · intro j hj hji
          exact ite_eq_right (fun hjp => hji (huniq j hj i hi hjp hp))
        · intro hnot
          exact (hnot hi).elim
      _ = 1 := ite_eq_left hp
  · rw [ite_eq_right hex]
    apply sum_eq_zero
    intro i hi
    exact ite_eq_right (fun hp => hex ⟨i, hi, hp⟩)

noncomputable def IsSafeSample (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (C T : Finset α) (parity : Bool) : Prop :=
  let b := nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d
  activation h + 2 ≤ b ∧ b ≤ 0 ∧ b % 2 = (if parity then 1 else 0) ∧
    d ∉ densityExpansion M hE κ (D h)
      (guardedPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (b-2) ∪
        lowerCompetition M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
          (fun i => (T : Set α) ∩ (G i : Set α)) b h)

omit [DecidableEq α] in
lemma isSafeSample_iff_endpoint (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (d : α) (C T : Finset α) (parity : Bool) :
    IsSafeSample M hE κ D G h d C T parity ↔ ∃ i ∈ range (pathHorizon h-1),
      safeBirthEvent M hE κ D G h d (-(i:ℤ)) C T ∧ (-(i:ℤ)) % 2 = (if parity then 1 else 0) := by
  let b := nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d
  have ht := activation_add_horizon h
  have hH := pathHorizon_pos h
  constructor
  · rintro ⟨hlo, hhi, hp, hs⟩
    have hi0 : 0 ≤ -b := by omega
    have hieq : -(((-b).toNat:ℕ):ℤ) = b := by rw [Int.toNat_of_nonneg hi0]; omega
    refine ⟨(-b).toNat, mem_range.mpr ?_, ?_, ?_⟩
    · have hiNat := Int.toNat_of_nonneg hi0
      change activation h + 2 ≤ b at hlo
      omega
    · rw [hieq]
      exact ⟨rfl, hs⟩
    · simpa only [hieq] using hp
  · rintro ⟨i, hi, hs, hp⟩
    have hbirth := hs.1
    have hbound := mem_range.mp hi
    change _ ∧ _ ∧ _ ∧ _
    rw [hbirth]
    exact ⟨by omega, by omega, hp, hs.2⟩

noncomputable def safeSampleSet (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) (parity : Bool) : Finset α :=
  I.filter (fun d => IsSafeSample M hE κ D G h d C T parity)

omit [DecidableEq α] in

lemma safeSampleCount_eq_card (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (h : ℕ) (I C T : Finset α) (parity : Bool) :
    safeSampleCount M hE κ D G h I C T parity = (safeSampleSet M hE κ D G h I C T parity).card := by
  unfold safeSampleCount safeSampleSet
  have hpoint (d : α) : safeEndpointParityCount M hE κ D G h d C T parity =
      if IsSafeSample M hE κ D G h d C T parity then 1 else 0 := by
    unfold safeEndpointParityCount
    rw [sum_unique_indicators]
    · simp only [← isSafeSample_iff_endpoint]
    · intro i hi j hj hsi hsj
      have hbi := hsi.1.1
      have hbj := hsj.1.1
      omega
  simp_rw [hpoint]
  simp

end MatroidProphet

end OAI
