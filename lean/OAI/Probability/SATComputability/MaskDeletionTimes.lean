import OAI.Probability.SATComputability.IncidentMasks
import OAI.Probability.SATComputability.DeletionEnergy

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

theorem maskLifetime_union {n m : ℕ} (U V : Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) :
    maskLifetime m (U ∪ V) xs = max (maskLifetime m U xs) (maskLifetime m V xs) := by
  induction m generalizing U V with
  | zero => simp [maskLifetime]
  | succ m ih =>
    by_cases hU : U.Nonempty
    · by_cases hV : V.Nonempty
      · have hUV : (U ∪ V).Nonempty := hU.mono Finset.subset_union_left
        simp only [maskLifetime, candidateAlive, ite_eq_left hU, ite_eq_left hV,
          ite_eq_left hUV, Finset.union_inter_distrib_right, ih, max_add_add_left]
      · have hVe : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
        subst V
        simp only [Finset.union_empty, maskLifetime_empty, max_eq_left (maskLifetime_nonneg U xs)]
    · have hUe : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      subst U
      simp only [Finset.empty_union, maskLifetime_empty, max_eq_right (maskLifetime_nonneg V xs)]

theorem maskLifetime_biUnion {ι : Type*} [DecidableEq ι] {n m : ℕ}
    (S : Finset ι) (hS : S.Nonempty) (F : ι → Finset (DeletionCandidate n))
    (xs : Fin m → Finset (DeletionCandidate n)) :
    maskLifetime m (S.biUnion F) xs = S.sup' hS (fun i => maskLifetime m (F i) xs) := by
  induction S using Finset.induction_on with
  | empty => simp at hS
  | @insert a S ha ih =>
    by_cases hne : S.Nonempty
    · rw [Finset.biUnion_insert, maskLifetime_union, ih hne, Finset.sup'_insert hne]
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst S
      simp

def deletionMask {n : ℕ} (D : Finset (Fin n)) : Finset (DeletionCandidate n) :=
  Finset.univ.filter (fun x => deletedVariables x ⊆ D)

def deletionBudgetMask (n r : ℕ) : Finset (DeletionCandidate n) :=
  Finset.univ.filter (fun x => (deletedVariables x).card ≤ r)

def freeDeletionBudgetMask (n r : ℕ) (v : Fin n) : Finset (DeletionCandidate n) :=
  (allowedDeletions n r).biUnion (fun D => deletionMask (insert v D))

theorem deletionMask_mono {n : ℕ} : Monotone (deletionMask (n := n)) := by
  intro D E hDE x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.trans hDE⟩

theorem deletionBudgetMask_union (n r : ℕ) :
    (allowedDeletions n r).biUnion (deletionMask (n := n)) = deletionBudgetMask n r := by
  ext x
  simp only [Finset.mem_biUnion, deletionMask, deletionBudgetMask, allowedDeletions,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨D,hD,hx⟩
    exact (Finset.card_le_card hx).trans hD
  · intro hx
    exact ⟨deletedVariables x,hx,Finset.Subset.refl _⟩

noncomputable def fixedMaskDeletionTime {n m : ℕ}
    (xs : Fin m → Finset (DeletionCandidate n)) (D : Finset (Fin n)) : ℝ :=
  maskLifetime m (deletionMask D) xs

theorem fixedMaskDeletionTime_mono {n m : ℕ}
    (xs : Fin m → Finset (DeletionCandidate n)) : Monotone (fixedMaskDeletionTime xs) := by
  intro D E hDE
  exact maskLifetime_mono (deletionMask_mono hDE) xs

theorem bestMaskDeletionTime_eq {n m : ℕ}
    (xs : Fin m → Finset (DeletionCandidate n)) (r : ℕ) :
    bestDeletionTime (fixedMaskDeletionTime xs) r = maskLifetime m (deletionBudgetMask n r) xs := by
  rw [← deletionBudgetMask_union, maskLifetime_biUnion _ (allowedDeletions_nonempty n r)]
  rfl

theorem freeMaskDeletionTime_eq {n m : ℕ}
    (xs : Fin m → Finset (DeletionCandidate n)) (r : ℕ) (v : Fin n) :
    freeDeletionTime (fixedMaskDeletionTime xs) r v = maskLifetime m (freeDeletionBudgetMask n r v) xs := by
  rw [freeDeletionBudgetMask, maskLifetime_biUnion _ (allowedDeletions_nonempty n r)]
  rfl

theorem maskLifetime_frontload {n m : ℕ} (U : Finset (DeletionCandidate n))
    (base incident : Fin m → Finset (DeletionCandidate n)) (I : Finset (DeletionCandidate n))
    (hI : ∀ j, I ⊆ incident j) :
    maskLifetime m (U ∩ I) base ≤ maskLifetime m U (fun j => base j ∩ incident j) := by
  induction m generalizing U with
  | zero => exact le_rfl
  | succ m ih =>
    simp only [maskLifetime]
    apply add_le_add (candidateAlive_mono Finset.inter_subset_left)
    have hsub : (U ∩ I) ∩ base 0 ⊆ (U ∩ (base 0 ∩ incident 0)) ∩ I := by
      intro x hx
      obtain ⟨hxUI,hxb⟩ := Finset.mem_inter.mp hx
      obtain ⟨hxU,hxI⟩ := Finset.mem_inter.mp hxUI
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
        ⟨hxU,Finset.mem_inter.mpr ⟨hxb,hI 0 hxI⟩⟩,hxI⟩
    exact (maskLifetime_mono hsub (Fin.tail base)).trans
      (ih (U ∩ (base 0 ∩ incident 0)) (Fin.tail base) (Fin.tail incident) (fun j => hI j.succ))

end FixedClauseThreshold.Computability

end OAI
