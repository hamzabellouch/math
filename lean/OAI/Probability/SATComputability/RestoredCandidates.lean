import OAI.Probability.SATComputability.MaskDeletionTimes

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

def restoreCandidate {n : ℕ} (b : Option Bool) (x : DeletionCandidate n) :
    DeletionCandidate (n+1) := Fin.cons b x

theorem deletedVariables_tail_image {n : ℕ} (x : DeletionCandidate (n+1)) :
    (deletedVariables (Fin.tail x)).image Fin.succ = (deletedVariables x).erase 0 := by
  ext i
  rw [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨j,hj,rfl⟩
    refine ⟨Fin.succ_ne_zero _,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
  · rintro ⟨hi0,hi⟩
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩,rfl⟩

theorem deletedVariables_restore_card {n : ℕ} (b : Bool) (x : DeletionCandidate n) :
    (deletedVariables (restoreCandidate (some b) x)).card = (deletedVariables x).card := by
  have h0 : (0 : Fin (n+1)) ∉ deletedVariables (restoreCandidate (some b) x) := by
    intro h
    have hx := (Finset.mem_filter.mp h).2
    simp [restoreCandidate] at hx
  have he := deletedVariables_tail_image (restoreCandidate (some b) x)
  rw [Finset.erase_eq_of_notMem h0] at he
  rw [← he, Finset.card_image_of_injective _ (Fin.succ_injective n)]
  rfl

theorem mem_freeDeletionBudgetMask {n r : ℕ} (x : DeletionCandidate (n+1)) :
    x ∈ freeDeletionBudgetMask (n+1) r 0 ↔
      (deletedVariables (Fin.tail x)).card ≤ r := by
  simp only [freeDeletionBudgetMask, Finset.mem_biUnion, allowedDeletions, deletionMask,
    Finset.mem_filter, Finset.mem_univ, true_and]
  have hc : ((deletedVariables (Fin.tail x)).image Fin.succ).card =
      (deletedVariables (Fin.tail x)).card := Finset.card_image_of_injective _ (Fin.succ_injective n)
  constructor
  · rintro ⟨D,hD,hx⟩
    have hsub : (deletedVariables (Fin.tail x)).image Fin.succ ⊆ D := by
      rw [deletedVariables_tail_image]
      intro i hi
      obtain ⟨hi0,hi⟩ := Finset.mem_erase.mp hi
      exact (Finset.mem_insert.mp (hx hi)).resolve_left hi0
    rw [← hc]
    exact (Finset.card_le_card hsub).trans hD
  · intro hx
    refine ⟨(deletedVariables (Fin.tail x)).image Fin.succ, by simpa only [hc] using hx, ?_⟩
    intro i hi
    by_cases hi0 : i = 0
    · exact Finset.mem_insert.mpr (Or.inl hi0)
    · exact Finset.mem_insert.mpr (Or.inr (by
        rw [deletedVariables_tail_image]
        exact Finset.mem_erase.mpr ⟨hi0,hi⟩))

theorem maskLifetime_map_le {n N m : ℕ} (f : DeletionCandidate n → DeletionCandidate N)
    (U : Finset (DeletionCandidate n)) (V : Finset (DeletionCandidate N))
    (xs : Fin m → Finset (DeletionCandidate n)) (ys : Fin m → Finset (DeletionCandidate N))
    (hUV : ∀ x ∈ U, f x ∈ V)
    (hxy : ∀ j x, x ∈ xs j → f x ∈ ys j) :
    maskLifetime m U xs ≤ maskLifetime m V ys := by
  induction m generalizing U V with
  | zero => exact le_rfl
  | succ m ih =>
    apply add_le_add
    · unfold candidateAlive
      split_ifs with hU hV hV
      · exact le_rfl
      · obtain ⟨x,hx⟩ := hU
        exact False.elim (hV ⟨f x,hUV x hx⟩)
      · norm_num
      · exact le_rfl
    · exact ih (U ∩ xs 0) (V ∩ ys 0) (Fin.tail xs) (Fin.tail ys)
        (fun x hx => Finset.mem_inter.mpr
          ⟨hUV x (Finset.mem_inter.mp hx).1,hxy 0 x (Finset.mem_inter.mp hx).2⟩)
        (fun j x hx => hxy j.succ x hx)

noncomputable def restoredMask {n : ℕ} (B F T : Finset (DeletionCandidate n)) :
    Finset (DeletionCandidate (n+1)) :=
  Finset.univ.filter (fun x => Fin.tail x ∈ B ∧
    match x 0 with
    | none => True
    | some false => Fin.tail x ∈ F
    | some true => Fin.tail x ∈ T)

theorem restoredMask_tail {n : ℕ} (B F T : Finset (DeletionCandidate n))
    {x : DeletionCandidate (n+1)} (hx : x ∈ restoredMask B F T) : Fin.tail x ∈ B :=
  (Finset.mem_filter.mp hx).2.1

theorem restore_none_mem {n : ℕ} (B F T : Finset (DeletionCandidate n))
    {x : DeletionCandidate n} (hx : x ∈ B) :
    restoreCandidate none x ∈ restoredMask B F T := by
  simpa [restoredMask, restoreCandidate] using hx

theorem restore_some_mem {n : ℕ} (B F T : Finset (DeletionCandidate n))
    (b : Bool) {x : DeletionCandidate n} (hx : x ∈ B)
    (hi : x ∈ if b then T else F) :
    restoreCandidate (some b) x ∈ restoredMask B F T := by
  cases b <;> simpa [restoredMask, restoreCandidate, hx] using hi

theorem free_restored_lifetime {n r m : ℕ}
    (base f t : Fin m → Finset (DeletionCandidate n)) :
    maskLifetime m (freeDeletionBudgetMask (n+1) r 0)
      (fun j => restoredMask (base j) (f j) (t j)) =
      maskLifetime m (deletionBudgetMask n r) base := by
  apply le_antisymm
  · apply maskLifetime_map_le (fun x => Fin.tail x)
    · intro x hx
      simpa only [deletionBudgetMask, Finset.mem_filter, Finset.mem_univ, true_and,
        mem_freeDeletionBudgetMask] using hx
    · intro j x hx
      exact restoredMask_tail _ _ _ hx
  · apply maskLifetime_map_le (restoreCandidate none)
    · intro x hx
      rw [mem_freeDeletionBudgetMask]
      simpa only [restoreCandidate, Fin.tail_cons, deletionBudgetMask,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    · intro j x hx
      exact restore_none_mem _ _ _ hx

theorem restored_frontload_lifetime {n r m : ℕ}
    (base f t : Fin m → Finset (DeletionCandidate n))
    (F T : Finset (DeletionCandidate n))
    (hF : ∀ j, F ⊆ f j) (hT : ∀ j, T ⊆ t j) :
    maskLifetime m (deletionBudgetMask n r ∩ (F ∪ T)) base ≤
      maskLifetime m (deletionBudgetMask (n+1) r)
        (fun j => restoredMask (base j) (f j) (t j)) := by
  rw [Finset.inter_union_distrib_left, maskLifetime_union]
  apply max_le
  · apply le_trans (maskLifetime_frontload _ base f F hF)
    apply maskLifetime_map_le (restoreCandidate (some false))
    · intro x hx
      simpa only [deletionBudgetMask, Finset.mem_filter, Finset.mem_univ, true_and,
        deletedVariables_restore_card] using hx
    · intro j x hx
      exact restore_some_mem _ _ _ false (Finset.mem_inter.mp hx).1
        (Finset.mem_inter.mp hx).2
  · apply le_trans (maskLifetime_frontload _ base t T hT)
    apply maskLifetime_map_le (restoreCandidate (some true))
    · intro x hx
      simpa only [deletionBudgetMask, Finset.mem_filter, Finset.mem_univ, true_and,
        deletedVariables_restore_card] using hx
    · intro j x hx
      exact restore_some_mem _ _ _ true (Finset.mem_inter.mp hx).1
        (Finset.mem_inter.mp hx).2

theorem deletionBudgetMask_subset_free (n r : ℕ) (v : Fin n) :
    deletionBudgetMask n r ⊆ freeDeletionBudgetMask n r v := by
  intro x hx
  apply Finset.mem_biUnion.mpr
  refine ⟨deletedVariables x, ?_, ?_⟩
  · simpa only [allowedDeletions, deletionBudgetMask, Finset.mem_filter,
      Finset.mem_univ, true_and] using hx
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_insert _ _⟩

theorem restored_gap_nonneg {n r m : ℕ}
    (base f t : Fin m → Finset (DeletionCandidate n)) :
    0 ≤ maskLifetime m (deletionBudgetMask n r) base -
      maskLifetime m (deletionBudgetMask (n+1) r)
        (fun j => restoredMask (base j) (f j) (t j)) := by
  rw [← free_restored_lifetime base f t]
  exact sub_nonneg.mpr (maskLifetime_mono (deletionBudgetMask_subset_free (n+1) r 0) _)

theorem restored_gap_bound {n r m : ℕ}
    (base f t : Fin m → Finset (DeletionCandidate n))
    (F T : Finset (DeletionCandidate n))
    (hF : ∀ j, F ⊆ f j) (hT : ∀ j, T ⊆ t j) :
    (maskLifetime m (deletionBudgetMask n r) base -
      maskLifetime m (deletionBudgetMask (n+1) r)
        (fun j => restoredMask (base j) (f j) (t j)))^(6/5 : ℝ) ≤
      (maskLifetime m (deletionBudgetMask n r) base -
        maskLifetime m (deletionBudgetMask n r ∩ (F ∪ T)) base)^(6/5 : ℝ) := by
  apply Real.rpow_le_rpow (restored_gap_nonneg base f t)
    (sub_le_sub_left (restored_frontload_lifetime base f t F T hF hT) _) (by norm_num)

end FixedClauseThreshold.Computability

end OAI
