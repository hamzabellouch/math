import OAI.Combinatorics.BalancedRyser.Construction.BlockPartitions
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Probability.PointEdgeInjective

namespace OAI

namespace Balanced.Configuration.BlockPartitions

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {C : Configuration F}

noncomputable def mergedDirectionsAt (C : Configuration F) (p : Point F) :
    Finset (Direction F) :=
  ((constituentLines C.merged).filter (OnLine p)).image Prod.fst

theorem mergedDirectionsAt_card_le (p : Point F) :
    (mergedDirectionsAt C p).card ≤
      ((constituentLines C.merged).filter (OnLine p)).card :=
  Finset.card_image_le

theorem mergedDirection_mem_of_block {p : Point F} {d : Direction F}
    (hp : p ∈ C.blockPoints (Sum.inr (Sum.inl d))) :
    d ∈ mergedDirectionsAt C p := by
  obtain ⟨b, hb⟩ := merged_block_onLine hp
  exact Finset.mem_image.mpr ⟨constituent C.merged d b,
    Finset.mem_filter.mpr ⟨constituent_mem d b, hb⟩, rfl⟩

theorem same_label_off_join_merged (hV : C.Valid) (hC : C.Compatible)
    (p q : {p // p ∈ C.points}) (hpq : p ≠ q) (d : Direction F)
    (hd : d ≠ (joiningLine p.val q.val).1)
    (heq : pointLabel hV hC d p = pointLabel hV hC d q) :
    d ∈ mergedDirectionsAt C p.val := by
  have hpq' : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  let b := pointLabel hV hC d p
  have hpb : p.val ∈ C.blockPoints b.val := pointLabel_mem hV hC d p
  have hqb : q.val ∈ C.blockPoints b.val := by
    change q.val ∈ C.blockPoints (pointLabel hV hC d p).val
    rw [heq]
    exact pointLabel_mem hV hC d q
  have hdir : blockDirection b.val = d := (Finset.mem_filter.mp b.property).2
  rcases hval : b.val with l | (g | ⟨s, c⟩)
  · rw [hval] at hpb hqb hdir
    have hl := eq_of_two_common_points p.val q.val hpq' l (joiningLine p.val q.val)
      (regular_block_onLine hpb) (regular_block_onLine hqb)
      (onLine_joiningLine_left _ _) (onLine_joiningLine_right _ _)
    exact (hd (hdir.symm.trans (congrArg Prod.fst hl))).elim
  · rw [hval] at hpb hdir
    have hm := mergedDirection_mem_of_block hpb
    simpa only [blockDirection] using hdir ▸ hm
  · rw [hval] at hpb hqb hdir
    have hl := eq_of_two_common_points p.val q.val hpq' (C.choice s).line
      (joiningLine p.val q.val) (split_block_onLine hV s c hpb)
      (split_block_onLine hV s c hqb)
      (onLine_joiningLine_left _ _) (onLine_joiningLine_right _ _)
    apply False.elim
    apply hd
    exact hdir.symm.trans ((split_direction hV s).symm.trans (congrArg Prod.fst hl))

theorem pointLabel_injective (hV : C.Valid) (hC : C.Compatible)
    {B : ℕ} (hB : B < Fintype.card F)
    (hocc : ∀ p, ((constituentLines C.merged).filter (OnLine p)).card ≤ B) :
    Function.Injective (fun p d => pointLabel hV hC d p) := by
  apply Balanced.point_assignment_injective_of_few_merged
    (pointLabel hV hC)
    (fun p q => (joiningLine p.val q.val).1)
    (fun p => mergedDirectionsAt C p.val)
  · intro p
    have hle := (mergedDirectionsAt_card_le (C := C) p.val).trans (hocc p.val)
    simp only [Direction, Fintype.card_option]
    omega
  · exact same_label_off_join_merged hV hC

theorem pointLabel_injective_of_occupancy (hV : C.Valid) (hC : C.Compatible)
    {ρ : ℝ} {B : ℕ} (hρ : ρ < 1) (hocc : C.Occupancy ρ B)
    (hsize : 2 * (1 + (B : ℝ)) < ρ * Fintype.card F) :
    Function.Injective (fun p d => pointLabel hV hC d p) := by
  apply pointLabel_injective hV hC
    (Balanced.multiplicity_lt_order_of_size_condition hρ (by positivity) hsize)
  exact hocc.1

end Balanced.Configuration.BlockPartitions

end OAI
