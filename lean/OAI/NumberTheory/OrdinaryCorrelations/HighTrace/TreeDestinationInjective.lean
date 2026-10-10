import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeVertices

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {h ℓ : ℕ}

lemma tree_destination_injective (w : ClosedLine h ℓ) :
    Set.InjOn (fun i : Fin ℓ => w.offset i.succ) w.treeSteps := by
  intro i hi j hj heq
  have hi' := (mem_filter.mp hi).2
  have hj' := (mem_filter.mp hj).2
  apply Fin.ext
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · exact hj' i.succ (by change i.val + 1 ≤ j.val; omega) heq
  · exact hi' j.succ (by change j.val + 1 ≤ i.val; omega) heq.symm

lemma tree_destination_nonzero (w : ClosedLine h ℓ) (i : Fin ℓ) (hi : i ∈ w.treeSteps) :
    w.offset i.succ ≠ 0 := by
  have h := (mem_filter.mp hi).2 0 (Nat.zero_le _)
  rwa [w.start_zero, ne_comm] at h

lemma has_incoming_edge (w : ClosedLine h ℓ) (v : ℤ)
    (hv : v ∈ treeVertices w) (hv0 : v ≠ 0) :
    ∃ i ∈ w.treeSteps, w.offset i.succ = v := by
  let visits : Finset (Fin (ℓ+1)) := univ.filter (fun j => w.offset j = v)
  have hn : visits.Nonempty := by
    obtain ⟨j,hj,hv⟩ := mem_image.mp hv
    exact ⟨j,mem_filter.mpr ⟨hj,hv⟩⟩
  let j := visits.min' hn
  have hj : w.offset j = v := (mem_filter.mp (min'_mem visits hn)).2
  have hj0 : j ≠ 0 := by
    intro heq
    rw [heq, w.start_zero] at hj
    exact hv0 hj.symm
  obtain ⟨i,hi⟩ := Fin.eq_succ_of_ne_zero hj0
  refine ⟨i,mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩
  · intro k hk hki
    have hkv : w.offset k = v := by rw [hki, ← hi]; exact hj
    have hkmin : j ≤ k := min'_le visits k (mem_filter.mpr ⟨mem_univ _,hkv⟩)
    have hkmin' : j.val ≤ k.val := hkmin
    rw [hi, Fin.val_succ] at hkmin'
    omega
  · rwa [← hi]

def goodOrigins (w : ClosedLine h ℓ) : Finset ℤ :=
  (univ.filter w.Good).image (fun i => w.offset i.castSucc)

lemma good_origin_data (w : ClosedLine h ℓ) {v : ℤ} (hv : v ∈ goodOrigins w) :
    v ∈ treeVertices w ∧ v ≠ 0 ∧ w.children v = 1 ∧ w.NoReturnIncidence v := by
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
  have hg := (mem_filter.mp hi).2
  exact ⟨departure_mem_vertices w i, hg.2.2.2.1, hg.2.1, hg.2.2.2.2.1⟩

def incomingCharges (w : ClosedLine h ℓ) (U : Finset ℤ) : Finset (Fin ℓ) :=
  w.treeSteps.filter (fun i => w.offset i.succ ∈ U)

def returnSteps (w : ClosedLine h ℓ) : Finset (Fin ℓ) := univ \ w.treeSteps

lemma incomingCharges_image (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hU : U ⊆ goodOrigins w) :
    (incomingCharges w U).image (fun i => w.offset i.succ) = U := by
  ext v
  constructor
  · rintro hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp hi).2
  · intro hv
    have hd := good_origin_data w (hU hv)
    obtain ⟨i,hi,hiv⟩ := has_incoming_edge w v hd.1 hd.2.1
    exact mem_image.mpr ⟨i,mem_filter.mpr ⟨hi,by rwa [hiv]⟩,hiv⟩

lemma incomingCharges_card (w : ClosedLine h ℓ) (U : Finset ℤ)
    (hU : U ⊆ goodOrigins w) : (incomingCharges w U).card = U.card := by
  calc
    _ = ((incomingCharges w U).image (fun i => w.offset i.succ)).card :=
      (card_image_iff.mpr ((tree_destination_injective w).mono (filter_subset _ _))).symm
    _ = U.card := congrArg Finset.card (incomingCharges_image w U hU)

lemma incoming_return_disjoint (w : ClosedLine h ℓ) (U : Finset ℤ) :
    Disjoint (incomingCharges w U) (returnSteps w) := by
  apply disjoint_left.mpr
  intro i hi hr
  exact (mem_sdiff.mp hr).2 (mem_filter.mp hi).1

theorem source_cutoff_charges {S : PrimeSystem} (w : ClosedLine h ℓ) {T : ℝ}
    (cut : S.Cutoffs T) (x : S.CoreResidues) (U : Finset ℤ)
    (hU : U ⊆ goodOrigins w) :
    S.cutoffProduct w cut x ≤
      Real.exp (-kappa * (S.harmonicCore - T * Real.sqrt S.harmonicCore) *
        (((returnSteps w).card : ℝ) + U.card)) *
      Real.exp (kappa *
        ((∑ i ∈ returnSteps w, (S.cutoffCount (w.label i)
          (S.shiftCore x (w.offset i.castSucc)) : ℝ)) +
         ∑ i ∈ incomingCharges w U, (S.cutoffCount (w.label i)
          (S.shiftCore x (w.offset i.succ)) : ℝ))) := by
  simpa only [incomingCharges_card w U hU] using
    cutoffProduct_le_charges w cut x (returnSteps w) (incomingCharges w U)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
