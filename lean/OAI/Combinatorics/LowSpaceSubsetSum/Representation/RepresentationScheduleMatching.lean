import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationMatchingWork
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScheduleUniverse

namespace OAI

/-! # Raw occurrence accounting across all lifted parent residues -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

namespace RepresentationScheduleData

variable {n g : ℕ} (D : RepresentationScheduleData n g)

def lowMatchingUniverse (side : Fin 2) :
    Finset (RepresentationUniverse.ParentOccurrence (Fin n)) :=
  (RepresentationUniverse.parents (D.leaves side)).filter (fun x =>
    RepresentationUniverse.parentWeight
      (flip (fun i => (D.input.values i : ℤ)) D.signs) x % (D.p0 : ℤ) =
        (if side = 0 then (D.rho0.val : ℤ) else D.target - D.rho0.val) % (D.p0 : ℤ) ∧
    RepresentationUniverse.childWeight
      (flip (fun i => (D.input.values i : ℤ)) D.signs) x.1 % (D.lowModuli side : ℤ) =
        D.firstResidues side % (D.lowModuli side : ℤ))

theorem matchingUniverse_subset_low (side : Fin 2) (z : ℕ) (P : MaskRestriction n) :
    ({ D.parentData side z with maskRestriction := P }).matchingUniverse ⊆
      D.lowMatchingUniverse side := by
  classical
  intro x hx
  let E := { D.parentData side z with maskRestriction := P }
  obtain ⟨hx, hy, hk⟩ := (E.matchingUniverse_mem x).mp hx
  have hparent := (E.key_match_iff x).mp hk
  have hd : (D.p0 : ℤ) ∣ D.modulus := dvd_mul_right _ _
  have hlow := congrArg (fun w : ℤ => w % (D.p0 : ℤ)) hparent
  change (RepresentationUniverse.parentWeight E.weights x % D.modulus) % (D.p0 : ℤ) =
    ((D.parentData side z).parentResidue % D.modulus) % (D.p0 : ℤ) at hlow
  rw [Int.emod_emod_of_dvd _ hd, Int.emod_emod_of_dvd _ hd,
    D.parentResidue_low side z] at hlow
  have hchild := (((E.pair 0).output_mem x.1).mp hx).2.2
  apply Finset.mem_filter.mpr
  exact ⟨E.streams_parent x.1 x.2 hx hy, hlow, hchild⟩

theorem matchingUniverses_disjoint (side : Fin 2) :
    Pairwise (fun z w : Fin D.q =>
      Disjoint (D.parentData side z.val).matchingUniverse
        (D.parentData side w.val).matchingUniverse) := by
  classical
  intro z w hne
  apply Finset.disjoint_left.mpr
  intro x hxz hxw
  have hz := ((D.parentData side z.val).key_match_iff x).mp
    (((D.parentData side z.val).matchingUniverse_mem x).mp hxz).2.2
  have hw := ((D.parentData side w.val).key_match_iff x).mp
    (((D.parentData side w.val).matchingUniverse_mem x).mp hxw).2.2
  exact hne (D.parentResidue_injective side (hz.symm.trans hw))

theorem sum_matchingUniverse_card (side : Fin 2) :
    ∑ z : Fin D.q, (D.parentData side z.val).matchingUniverse.card ≤
      (D.lowMatchingUniverse side).card := by
  classical
  have hd : ((Finset.univ : Finset (Fin D.q)) : Set (Fin D.q)).PairwiseDisjoint
      (fun z => (D.parentData side z.val).matchingUniverse) := by
    intro z _ w _ hne
    exact D.matchingUniverses_disjoint side hne
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨z, _, hx⟩ := Finset.mem_biUnion.mp hx
  exact D.matchingUniverse_subset_low side z.val MaskRestriction.empty hx

/-- Child stream membership is independent of the full parent-residue counter. -/
theorem unrestrictedChildCount_eq_zero (side : Fin 2) (z : ℕ) :
    (D.parentData side z).unrestrictedChildCount =
      (D.parentData side 0).unrestrictedChildCount := rfl

end RepresentationScheduleData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)
variable (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
variable (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
variable (q : ℕ) (hq : 0 < q)

theorem schedule_lowMatchingUniverse_card (side : Fin 2) :
    ((R.scheduleData h r hn hlog q hq).lowMatchingUniverse side).card =
      if side = 0 then RepresentationMoments.JL (prefixModulus_pos h.2 0)
        (prefixModulus_pos h.2 1) (R.signedWeights h.1.1.1)
        (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) 0) r
      else RepresentationMoments.JR (prefixModulus_pos h.2 0) (prefixModulus_pos h.2 2)
        (R.signedWeights h.1.1.1)
        (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) 1)
        (R.signedTarget h.1.1.1) r := by
  classical
  fin_cases side
  all_goals
    simp only [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl,
      show (⟨1, by decide⟩ : Fin 2) = 1 from rfl, ite_true,
      ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
    apply congrArg Finset.card
    ext x
    simp only [RepresentationScheduleData.lowMatchingUniverse,
      twiceResidueFiltered, Finset.mem_filter,
      normalizedResidue_eq_iff, ResidueMatchAccounting.complement_val]
  · change (_ ∧ _ = (r.1.val : ℤ) % (prefixModulus h.2.val 0 : ℤ) ∧
        _ = (r.2.1.val : ℤ) % (prefixModulus h.2.val 1 : ℤ)) ↔
      (_ ∧ _ = (r.1.val : ℤ) ∧ _ = (r.2.1.val : ℤ))
    have h0 : (r.1.val : ℤ) % (prefixModulus h.2.val 0 : ℤ) = r.1.val :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.1.isLt)
    have h1 : (r.2.1.val : ℤ) % (prefixModulus h.2.val 1 : ℤ) = r.2.1.val :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.2.1.isLt)
    rw [h0, h1]
    rfl
  · change (_ ∧ _ = _ ∧ _ = (r.2.2.val : ℤ) % (prefixModulus h.2.val 2 : ℤ)) ↔
      (_ ∧ _ = _ ∧ _ = (r.2.2.val : ℤ))
    have h2 : (r.2.2.val : ℤ) % (prefixModulus h.2.val 2 : ℤ) = r.2.2.val :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.2.2.isLt)
    rw [h2]
    rfl

/-- Full-residue iteration and prefix recomputation multiply the raw tuple
resource charge only by the top-mask length. -/
theorem schedule_matchingVisits_sum_bound (B : ℕ) (side : Fin 2) :
    ∑ z : Fin q, ((R.scheduleData h r hn hlog q hq).parentData side z.val).matchingVisits B
      (R.scheduleData h r hn hlog q hq).topOrder MaskRestriction.empty ≤
        (mixerSize n + 1) *
          ((R.scheduleData h r hn hlog q hq).lowMatchingUniverse side).card := by
  let D := R.scheduleData h r hn hlog q hq
  calc
    _ ≤ ∑ z : Fin q, (mixerSize n + 1) * (D.parentData side z.val).matchingUniverse.card := by
      apply Finset.sum_le_sum
      intro z _
      have hm := (D.parentData side z.val).matchingVisits_le B
        (R.schedule_top_disjoint h r hn hlog q hq z.val side) D.topOrder
        (R.schedule_topOrder_mem h r hn hlog q hq z.val side) MaskRestriction.empty
      have he : { D.parentData side z.val with maskRestriction := MaskRestriction.empty } =
          D.parentData side z.val := rfl
      rw [he, R.schedule_topOrder_length h r hn hlog q hq] at hm
      exact hm
    _ = (mixerSize n + 1) * ∑ z : Fin q, (D.parentData side z.val).matchingUniverse.card :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (D.sum_matchingUniverse_card side)

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
