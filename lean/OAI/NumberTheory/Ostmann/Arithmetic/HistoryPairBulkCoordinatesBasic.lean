import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantSourceBoundsPair
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairGiantCoordinatesBasic
import OAI.NumberTheory.Ostmann.Conclusion.BulkPositionShape
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportSources

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairBulkCoordinates
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairGiantCoordinates
open HistoryRepeatedRenaming HistoryActiveCoordinates
attribute [local instance] Classical.propDecidable
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

abbrev RootBulkPosition (h : History l) :=
  {i : Fin h.root.small.length // (h.root.small.get i).role = .bulk}

def rootKey (h k : History l) (i : Fin h.root.small.length) : PairKey h k :=
  leftMap h k (.inr (.inl i))

def bulkCoordinates (h k : History l) : Finset (PairKey h k) :=
  Finset.univ.image (fun i : RootBulkPosition h => rootKey h k i.val)

theorem root_value_injective (h : History l) (hs : h.Supported V outside) :
    Function.Injective (fun i : Fin h.root.small.length => (h.root.small.get i).value) := by
  have hc := History.supported_root_coprime hs
  have hp : (h.root.small.map SmallSlot.value).Pairwise Nat.Coprime :=
    ((List.pairwise_append.mp hc).1.of_cons).of_cons
  have hprime : h.root.PrimeSmall := by
    rw [History.Supported.eq_def] at hs
    exact hs.2.1
  have hn : (h.root.small.map SmallSlot.value).Nodup := hp.imp_of_mem
    (fun {a b} ha hb hab he => by
      subst b
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
      exact (hprime q hq).ne_one
        (by simpa only [Nat.Coprime, Nat.gcd_self] using hab))
  have hfn : (List.ofFn (fun i : Fin h.root.small.length => (h.root.small.get i).value)).Nodup := by
    simpa only [List.get_eq_getElem, List.ofFn_getElem_eq_map] using hn
  exact List.nodup_ofFn.mp hfn

theorem rootKey_injective (h k : History l) (hs : h.Supported V outside) :
    Function.Injective (rootKey h k) := by
  intro i j he
  have hv := congrArg (pairSample h k) he
  simp only [rootKey, leftMap_sample, integerSample] at hv
  exact root_value_injective h hs (by exact_mod_cast hv)

def bulkEquiv (h k : History l) (hs : h.Supported V outside) :
    RootBulkPosition h ≃ bulkCoordinates h k :=
  Equiv.ofBijective (fun i => ⟨rootKey h k i.val,
    Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩) ⟨by
      intro i j he
      exact Subtype.ext (rootKey_injective h k hs (congrArg Subtype.val he)), by
      intro j
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp j.property
      exact ⟨i,Subtype.ext he⟩⟩

@[simp] theorem bulkEquiv_val (h k : History l) (hs : h.Supported V outside)
    (i : RootBulkPosition h) : (bulkEquiv h k hs i).val = rootKey h k i.val := rfl

theorem left_giant_not_mem (h k : History l) (b : Bool) :
    leftMap h k (.inl b) ∉ bulkCoordinates h k := by
  intro hm
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hm
  have hv := congrArg Subtype.val he
  cases hv

theorem right_giant_not_mem (h k : History l) (b : Bool) :
    rightMap h k (.inl b) ∉ bulkCoordinates h k := by
  rw [← shared_giant]
  exact left_giant_not_mem h k b

theorem left_nonbulk_not_mem (h k : History l) (hs : h.Supported V outside)
    (i : Fin h.root.small.length) (hi : (h.root.small.get i).role ≠ .bulk) :
    rootKey h k i ∉ bulkCoordinates h k := by
  intro hm
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hm
  have he' := rootKey_injective h k hs he
  exact hi (he' ▸ j.property)

theorem left_internal_not_mem (h k : History l) (i : InternalKey h) :
    leftMap h k (.inr (.inr i)) ∉ bulkCoordinates h k := by
  intro hm
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hm
  have hh := congrArg (pairLevel h k) he
  simp only [rootKey, leftMap_level, keyLevel, Sum.elim_inr, Sum.elim_inl] at hh
  have hb := (internalLevel_pos_le h i).2
  omega

theorem right_internal_not_mem (h k : History l) (i : InternalKey k) :
    rightMap h k (.inr (.inr i)) ∉ bulkCoordinates h k := by
  intro hm
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hm
  have hh := congrArg (pairLevel h k) he
  simp only [rootKey, leftMap_level, rightMap_level, keyLevel, Sum.elim_inr, Sum.elim_inl] at hh
  have hb := (internalLevel_pos_le k i).2
  omega

end Ostmann.Arithmetic.HistoryPairBulkCoordinates

end

end OAI
