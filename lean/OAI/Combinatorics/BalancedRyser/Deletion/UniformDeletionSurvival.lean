import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import OAI.Combinatorics.BalancedRyser.Deletion.DeletionProbability
import OAI.Combinatorics.BalancedRyser.Incidence.AffineUniformCoordinates

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.UniformDeletion

variable {F : Type*} [Fintype F] [DecidableEq F]

def offsets (D : Finset (Line F)) (d : Direction F) : Finset F :=
  Finset.univ.filter fun a => (d, a) ∈ D

@[simp] theorem mem_offsets (D : Finset (Line F)) (d : Direction F) (a : F) :
    a ∈ offsets D d ↔ (d, a) ∈ D := by
  simp [offsets]

theorem image_offsets (D : Finset (Line F)) (d : Direction F) :
    (offsets D d).image (fun a => (d, a)) = D.filter (fun l => l.1 = d) := by
  ext l
  rcases l with ⟨e, a⟩
  simp only [Finset.mem_image, mem_offsets, Prod.mk.injEq, Finset.mem_filter]
  constructor
  · rintro ⟨b, hb, rfl, rfl⟩
    exact ⟨hb, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ha, rfl, rfl⟩

theorem card_offsets (D : Finset (Line F)) (d : Direction F) :
    (offsets D d).card = (D.filter (fun l => l.1 = d)).card := by
  rw [← image_offsets, Finset.card_image_of_injective]
  intro a b h
  exact (Prod.mk.inj h).2

def ofOffsets (A : Direction F → Finset F) : Finset (Line F) :=
  Finset.univ.filter fun l => l.2 ∈ A l.1

@[simp] theorem mem_ofOffsets (A : Direction F → Finset F) (l : Line F) :
    l ∈ ofOffsets A ↔ l.2 ∈ A l.1 := by
  simp [ofOffsets]

@[simp] theorem offsets_ofOffsets (A : Direction F → Finset F) (d : Direction F) :
    offsets (ofOffsets A) d = A d := by
  ext a
  simp

@[simp] theorem ofOffsets_offsets (D : Finset (Line F)) :
    ofOffsets (offsets D) = D := by
  ext l
  rcases l with ⟨d, a⟩
  simp

variable [Field F]

def offsetEquiv (k : ℕ) :
    DeletionSet F k ≃ (Direction F → {s : Finset F // s.card = k}) where
  toFun D d := ⟨offsets D.val d, (card_offsets D.val d).trans (D.property d)⟩
  invFun A := ⟨ofOffsets (fun d => (A d).val), by
    intro d
    rw [← card_offsets, offsets_ofOffsets]
    exact (A d).property⟩
  left_inv D := Subtype.ext (ofOffsets_offsets D.val)
  right_inv A := by
    funext d
    apply Subtype.ext
    exact offsets_ofOffsets (fun d => (A d).val) d

theorem card_deletionSet (k : ℕ) :
    Fintype.card (DeletionSet F k) =
      (Fintype.card F).choose k ^ (Fintype.card F + 1) := by
  rw [Fintype.card_congr (offsetEquiv (F := F) k), Fintype.card_fun,
    Fintype.card_finset_len]
  simp [Direction]

def forbiddenOffsets (U : Finset (Point F)) (d : Direction F) : Finset F :=
  U.image (lineEval d)

theorem survives_iff (D : Finset (Line F)) (U : Finset (Point F)) :
    U ⊆ uncoveredBy D ↔
      ∀ d, Disjoint (offsets D d) (forbiddenOffsets U d) := by
  constructor
  · intro h d
    rw [Finset.disjoint_left]
    intro a ha hU
    obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp hU
    have hpD := (Finset.mem_filter.mp (h hp)).2
    exact hpD (d, a) ((mem_offsets D d a).mp ha) hpa
  · intro h p hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro l hl hpl
    exact Finset.disjoint_left.mp (h l.1)
      ((mem_offsets D l.1 l.2).mpr hl)
      (Finset.mem_image.mpr ⟨p, hp, hpl⟩)

def avoidingEquiv (T : Finset F) (k : ℕ) :
    {s : {s : Finset F // s.card = k} // Disjoint s.val T} ≃
      ↥((Finset.univ \ T).powersetCard k) where
  toFun s := ⟨s.val.val, Finset.mem_powersetCard.mpr ⟨by
    intro a ha
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hT => Finset.disjoint_left.mp s.property ha hT⟩, s.val.property⟩⟩
  invFun s := ⟨⟨s.val, (Finset.mem_powersetCard.mp s.property).2⟩, by
    rw [Finset.disjoint_left]
    intro a ha hT
    exact (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp s.property).1 ha)).2 hT⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Field F] in
theorem card_avoiding (T : Finset F) (k : ℕ) :
    Fintype.card {s : {s : Finset F // s.card = k} // Disjoint s.val T} =
      (Fintype.card F - T.card).choose k := by
  rw [Fintype.card_congr (avoidingEquiv T k), Fintype.card_coe,
    Finset.card_powersetCard,
    Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ]

theorem card_surviving (U : Finset (Point F)) (k : ℕ) :
    Fintype.card {D : DeletionSet F k // U ⊆ uncoveredBy D.val} =
      ∏ d : Direction F,
        (Fintype.card F - (forbiddenOffsets U d).card).choose k := by
  let e : {D : DeletionSet F k // U ⊆ uncoveredBy D.val} ≃
      {A : Direction F → {s : Finset F // s.card = k} //
        ∀ d, Disjoint (A d).val (forbiddenOffsets U d)} :=
    Equiv.subtypeEquiv (offsetEquiv (F := F) k) (fun D => survives_iff D.val U)
  rw [Fintype.card_congr e,
    Fintype.card_congr (Equiv.subtypePiEquivPi
      (β := fun _ : Direction F => {s : Finset F // s.card = k})
      (p := fun d s => Disjoint s.val (forbiddenOffsets U d))), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro d _
  exact card_avoiding (forbiddenOffsets U d) k

theorem nonempty_deletionSet_iff (k : ℕ) :
    Nonempty (DeletionSet F k) ↔ k ≤ Fintype.card F := by
  rw [← Fintype.card_pos_iff, card_deletionSet]
  constructor
  · intro h
    by_contra hk
    rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk), zero_pow (by omega)] at h
    omega
  · intro hk
    exact pow_pos (Nat.choose_pos hk) _

def law (k : ℕ) (hk : k ≤ Fintype.card F) : PMF (DeletionSet F k) := by
  letI := (nonempty_deletionSet_iff (F := F) k).mpr hk
  exact PMF.uniformOfFintype (DeletionSet F k)

theorem law_map_offsets (k : ℕ) (hk : k ≤ Fintype.card F) :
    letI : Nonempty {s : Finset F // s.card = k} :=
      Fintype.card_pos_iff.mp (by simpa using Nat.choose_pos hk)
    (law k hk).map (offsetEquiv (F := F) k) =
      PMF.uniformOfFintype (Direction F → {s : Finset F // s.card = k}) := by
  let : Nonempty {s : Finset F // s.card = k} :=
    Fintype.card_pos_iff.mp (by simpa using Nat.choose_pos hk)
  let := (nonempty_deletionSet_iff (F := F) k).mpr hk
  exact PairEvaluation.uniform_map_equiv (offsetEquiv (F := F) k)

theorem uniformMass_eq (k : ℕ) :
    uniformDeletionMass (F := F) k =
      (((Fintype.card F).choose k : ℝ) ^ (Fintype.card F + 1))⁻¹ := by
  simp only [uniformDeletionMass, card_deletionSet, Nat.cast_pow, one_div]

theorem surviving_probability (U : Finset (Point F)) (k : ℕ)
    [Nonempty (DeletionSet F k)] :
    deletionEventProbability (PMF.uniformOfFintype (DeletionSet F k))
      (fun D => U ⊆ uncoveredBy D.val) =
        ∏ d : Direction F,
          (((Fintype.card F - (forbiddenOffsets U d).card).choose k : ℝ) /
            ((Fintype.card F).choose k : ℝ)) := by
  classical
  have hc := card_surviving (F := F) U k
  rw [Fintype.card_subtype] at hc
  rw [deletionEventProbability_eq_outerMeasure,
    PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [Fintype.card_subtype, Set.mem_ofPred_eq,
    hc, card_deletionSet, Nat.cast_prod, Nat.cast_pow]
  rw [Finset.prod_div_distrib]
  simp [Direction]

theorem law_surviving_probability (U : Finset (Point F)) (k : ℕ)
    (hk : k ≤ Fintype.card F) :
    deletionEventProbability (law k hk) (fun D => U ⊆ uncoveredBy D.val) =
        ∏ d : Direction F,
          (((Fintype.card F - (forbiddenOffsets U d).card).choose k : ℝ) /
            ((Fintype.card F).choose k : ℝ)) := by
  let := (nonempty_deletionSet_iff (F := F) k).mpr hk
  exact surviving_probability U k

theorem point_survival (p : Point F) (k : ℕ) (hk : k ≤ Fintype.card F) :
    deletionEventProbability (law k hk) (fun D => p ∈ uncoveredBy D.val) =
      (((Fintype.card F - 1).choose k : ℝ) / ((Fintype.card F).choose k : ℝ)) ^
        (Fintype.card F + 1) := by
  simpa [forbiddenOffsets, Direction, div_pow] using law_surviving_probability {p} k hk

omit [DecidableEq F] in

theorem one_offset_ratio (k : ℕ) (hk : k ≤ Fintype.card F) :
    ((Fintype.card F - 1).choose k : ℝ) / ((Fintype.card F).choose k : ℝ) =
      1 - (k : ℝ) / Fintype.card F := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hqR : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hc : ((Fintype.card F).choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have h := Nat.choose_mul_succ_eq (Fintype.card F - 1) k
  rw [Nat.sub_add_cancel hq] at h
  have hR : ((Fintype.card F - 1).choose k : ℝ) * Fintype.card F =
      ((Fintype.card F).choose k : ℝ) * ((Fintype.card F : ℝ) - k) := by
    exact_mod_cast h
  apply (div_eq_iff hc).mpr
  field_simp
  nlinarith [hR]

theorem point_survival_eq (p : Point F) (k : ℕ) (hk : k ≤ Fintype.card F) :
    deletionEventProbability (law k hk) (fun D => p ∈ uncoveredBy D.val) =
      (1 - (k : ℝ) / Fintype.card F) ^ (Fintype.card F + 1) := by
  rw [point_survival, one_offset_ratio k hk]

theorem expected_core_card_sum {k : ℕ} (Q : PMF (DeletionSet F k)) :
    (∑ D, (Q D).toReal * ((uncoveredBy D.val).card : ℝ)) =
      ∑ p : Point F, deletionEventProbability Q (fun D => p ∈ uncoveredBy D.val) := by
  classical
  have hcard (D : DeletionSet F k) :
      ((uncoveredBy D.val).card : ℝ) =
        ∑ p : Point F, if p ∈ uncoveredBy D.val then (1 : ℝ) else 0 := by
    simp
  simp_rw [hcard, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  unfold deletionEventProbability
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro D _
  split_ifs <;> rfl

theorem expected_core_card (k : ℕ) (hk : k ≤ Fintype.card F) :
    (∑ D, (law k hk D).toReal * ((uncoveredBy D.val).card : ℝ)) =
      (Fintype.card F : ℝ) ^ 2 *
        (1 - (k : ℝ) / Fintype.card F) ^ (Fintype.card F + 1) := by
  rw [expected_core_card_sum]
  simp_rw [point_survival_eq _ k hk]
  simp [Point, pow_two]

end Balanced.UniformDeletion

end

end OAI
