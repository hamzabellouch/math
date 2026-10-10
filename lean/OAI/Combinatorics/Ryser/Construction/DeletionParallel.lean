import OAI.Combinatorics.Ryser.Construction.DeletionUnionBasic
import OAI.Combinatorics.Ryser.Construction.GroupPlacement

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {G k F : Type*} [Field k] [Field F]
variable [Fintype G] [Fintype k] [Fintype F]
variable [DecidableEq G] [DecidableEq k] [DecidableEq F]

theorem deletedLines_inter_affinePencil_infinite_eq_filter
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (a : GadgetOutcome k) (d : Direction F) :
    deletedLines σ M b a ∩ affinePencil (Sum.inr d) =
      (deletedLines σ M b a).filter (fun ell => ell.1 = d) := by
  ext ell
  simp only [Finset.mem_inter, Finset.mem_filter, mem_affinePencil,
    projectiveIncidence_infinite_affine]
  constructor <;> rintro ⟨hmem, hdir⟩ <;> exact ⟨hmem, hdir.symm⟩

theorem card_deletedLines_inter_affinePencil_infinite
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (d : Direction F)
    (hd : d ∈ alteredDirections σ M) :
    (deletedLines σ M b a ∩ affinePencil (Sum.inr d)).card =
      Fintype.card k - 1 := by
  rw [deletedLines_inter_affinePencil_infinite_eq_filter]
  exact card_deletedLines_of_mem_alteredDirections σ M b a ha d hd

theorem allDeletedLines_inter_affinePencil_infinite_eq_biUnion
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (d : Direction F) :
    allDeletedLines σ M b a ∩ affinePencil (Sum.inr d) =
      (Finset.univ.filter (fun i => d ∈ alteredDirections σ (M i))).biUnion
        (fun i => deletedLines σ (M i) (b i) a ∩ affinePencil (Sum.inr d)) := by
  ext ell
  constructor
  · intro hell
    obtain ⟨hglobal, hpencil⟩ := Finset.mem_inter.mp hell
    obtain ⟨i, hi⟩ := (mem_allDeletedLines σ M b a ell).mp hglobal
    have hdell : d = ell.1 := (mem_affinePencil (Sum.inr d) ell).mp hpencil
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ?_⟩, Finset.mem_inter.mpr ⟨hi, hpencil⟩⟩
    rw [hdell]
    exact ((mem_deletedLines σ (M i) (b i) a ell).mp hi).1
  · intro hell
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hell
    obtain ⟨hlocal, hpencil⟩ := Finset.mem_inter.mp hi
    exact Finset.mem_inter.mpr
      ⟨(mem_allDeletedLines σ M b a ell).mpr ⟨i, hlocal⟩, hpencil⟩

theorem card_allDeletedLines_inter_affinePencil_infinite_le
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (d : Direction F) :
    (allDeletedLines σ M b a ∩ affinePencil (Sum.inr d)).card ≤
      (Finset.univ.filter (fun i => d ∈ alteredDirections σ (M i))).card *
        (Fintype.card k - 1) := by
  rw [allDeletedLines_inter_affinePencil_infinite_eq_biUnion]
  refine Finset.card_biUnion_le.trans (le_of_eq ?_)
  exact Finset.sum_const_nat (fun i hi =>
    card_deletedLines_inter_affinePencil_infinite σ (M i) (b i) a ha d
      (Finset.mem_filter.mp hi).2)

theorem card_groupDeletedLines_inter_affinePencil_infinite_le_two
    (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (b : ConfigurationGroup σ → Point F) (a : GadgetOutcome k)
    (ha : OriginalLineDensity a) (d : Direction F) :
    (allDeletedLines σ (groupPlacement σ u v huv) b a ∩
      affinePencil (Sum.inr d)).card ≤ 2 * (Fintype.card k - 1) := by
  classical
  have hmult : (Finset.univ.filter (fun i =>
      d ∈ alteredDirections σ (groupPlacement σ u v huv i))).card ≤ 2 := by
    apply (Finset.card_le_card ?_).trans (groupAltered_multiplicity_le_two σ u v huv d)
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
  exact (card_allDeletedLines_inter_affinePencil_infinite_le
    σ (groupPlacement σ u v huv) b a ha d).trans
      (Nat.mul_le_mul_right _ hmult)

end RyserCoveringCounterexample.Construction

end

end OAI
