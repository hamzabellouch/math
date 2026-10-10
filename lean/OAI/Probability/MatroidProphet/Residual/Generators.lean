import OAI.Probability.MatroidProphet.Density.Birth

namespace OAI

namespace MatroidProphet

open Set

variable {α : Type*} [Fintype α]

lemma monotone_set_timing
    {α : Type u_1} [Fintype α] (J : ℕ → Set α) (hJ : Monotone J) (N : ℕ) :
    ∃ τ : α → ℕ, ∀ j ≤ N, J j = {g | g ∈ J N ∧ τ g ≤ j} := by
  classical
  let hex := fun g (hg : g ∈ J N) => show ∃ j, g ∈ J j from ⟨N, hg⟩
  let τ := fun g => if hg : g ∈ J N then Nat.find (hex g hg) else 0
  refine ⟨τ, ?_⟩
  intro j hj
  ext g
  constructor
  · intro hg
    have hgN := hJ hj hg
    refine ⟨hgN, ?_⟩
    simpa [τ, hgN] using Nat.find_min' (hex g hgN) hg
  · rintro ⟨hgN, hτ⟩
    have hfind : Nat.find (hex g hgN) ≤ j := by simpa [τ, hgN] using hτ
    exact hJ hfind (Nat.find_spec (hex g hgN))

lemma nominalPath_timed_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ) :
    ∃ G : Set α, G ⊆ D h ∧ κ * G.ncard ≤ (D h).ncard ∧ ∃ τ : α → ℕ,
      (∀ g ∈ G, τ g ≤ pathHorizon h) ∧
      (∀ j ≤ pathHorizon h,
        M.closure (guardedPath M hE κ D C h (activation h + j) ∪
          {g | g ∈ G ∧ τ g ≤ j}) = nominalPath M hE κ D C h (activation h + j)) := by
  obtain ⟨G, hGD, hGcard, J, hJmono, hJG, hgen⟩ := nominalPath_generators M hE κ hκ D C h
  obtain ⟨τ, hτ⟩ := monotone_set_timing J hJmono (pathHorizon h)
  refine ⟨J (pathHorizon h), (hJG _ le_rfl).trans hGD, ?_, τ, ?_, ?_⟩
  · exact (Nat.mul_le_mul_left κ (Set.ncard_mono (hJG _ le_rfl))).trans hGcard
  · intro g hg
    exact ((Set.ext_iff.mp (hτ _ le_rfl) g).mp hg).2
  · intro j hj
    rw [← hτ j hj]
    exact hgen j hj

noncomputable def timedGeneratorSet (G : Set α) (τ : α → ℕ) (a k : ℤ) : Set α :=
  {g | g ∈ G ∧ a + (τ g : ℤ) ≤ k}

lemma nominalPath_all_time_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ) :
    ∃ G : Set α, G ⊆ D h ∧ κ * G.ncard ≤ (D h).ncard ∧ ∃ τ : α → ℕ,
      (∀ g ∈ G, τ g ≤ pathHorizon h) ∧ ∀ k : ℤ,
        nominalPath M hE κ D C h k =
          M.closure (guardedPath M hE κ D C h k ∪ timedGeneratorSet G τ (activation h) k) := by
  obtain ⟨G, hGD, hGcard, τ, hbound, hgen⟩ := nominalPath_timed_generators M hE κ hκ D C h
  refine ⟨G, hGD, hGcard, τ, hbound, ?_⟩
  intro k
  by_cases hka : k < activation h
  · have hearly : k < -3 * (h : ℤ) - 1 := by
      dsimp [activation] at hka
      omega
    have hempty : timedGeneratorSet G τ (activation h) k = ∅ := by
      ext g
      simp only [timedGeneratorSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ htime
      omega
    rw [nominalPath_early M hE κ D C h hka, guardedPath_early M hE κ D C h hearly,
      hempty, union_empty, M.closure_closure]
  · by_cases hk0 : 0 ≤ k
    · rw [nominalPath_nonnegative M hE κ D C h hk0, guardedPath_nonnegative M hE κ D C h hk0]
      simp [M.closure_univ, hE]
    · let j := (k - activation h).toNat
      have hjcast : (j : ℤ) = k - activation h := Int.toNat_of_nonneg (by omega)
      have hj : j ≤ pathHorizon h := by
        have hhor := activation_add_horizon h
        omega
      have hkj : activation h + (j : ℤ) = k := by omega
      have hsets : {g | g ∈ G ∧ τ g ≤ j} = timedGeneratorSet G τ (activation h) k := by
        ext g
        simp only [timedGeneratorSet, Set.mem_ofPred_eq]
        constructor <;> rintro ⟨hg, ht⟩ <;> exact ⟨hg, by omega⟩
      have h := hgen j hj
      rw [hkj, hsets] at h
      exact h.symm

end MatroidProphet

end OAI
