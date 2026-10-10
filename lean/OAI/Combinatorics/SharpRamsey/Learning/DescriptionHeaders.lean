import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialCover
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialPrepared

namespace OAI

section
namespace SharpLogRamsey.DescriptionHeaders
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem card_submodule_le :
    Nat.card (Submodule K V)≤(Nat.card K)^(Module.finrank K V)^2 := by
  let : Finite V := Module.finite_of_finite K
  let : Finite (V→ₗ[K]V) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have hs : Function.Surjective (LinearMap.range : (V→ₗ[K]V)→Submodule K V) := by
    intro W
    obtain ⟨Q,hQ⟩ := W.exists_isCompl
    exact ⟨W.projection Q hQ,W.range_projection hQ⟩
  apply (Nat.card_le_card_of_surjective _ hs).trans_eq
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (V→ₗ[K]V) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card,Module.finrank_linearMap,pow_two] using
    (Module.card_eq_pow_finrank (K:=K) (V:=V→ₗ[K]V))

variable {α : Type*} [Fintype α]

def headers (J N : ℕ) : Finset (List (α×ℕ)) :=
  (range (J+1)).biUnion (fun m =>
    (univ : Finset (Fin m→α×Fin (N+1))).image
      (fun v => List.ofFn (fun i => ((v i).1,((v i).2:ℕ)))))

lemma mem_headers_iff (J N : ℕ) (bs : List (α×ℕ)) :
    bs∈headers J N ↔ bs.length≤J ∧ ∀ h∈bs,h.2≤N := by
  constructor
  · intro hb
    obtain ⟨m,hm,hv⟩ := mem_biUnion.mp hb
    obtain ⟨v,_,rfl⟩ := mem_image.mp hv
    constructor
    · simpa only [List.length_ofFn] using Nat.le_of_lt_succ (mem_range.mp hm)
    · intro h hh
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
      exact Nat.le_of_lt_succ (v i).2.isLt
  · rintro ⟨hlen,hsize⟩
    let v : Fin bs.length→α×Fin (N+1) := fun i =>
      ((bs.get i).1,⟨(bs.get i).2,Nat.lt_succ_of_le (hsize _ (List.get_mem _ _))⟩)
    refine mem_biUnion.mpr ⟨bs.length,mem_range.mpr (by omega),mem_image.mpr ⟨v,mem_univ _,?_⟩⟩
    simpa only [v] using List.ofFn_get bs

lemma card_headers_le (J N : ℕ) :
    (headers (α:=α) J N).card≤(J+1)*(Fintype.card α*(N+1)+1)^J := by
  apply (card_biUnion_le).trans
  calc
    _ ≤ ∑ m∈range (J+1),(Fintype.card α*(N+1))^m := by
      apply sum_le_sum
      intro m _
      exact (card_image_le).trans_eq (by simp)
    _ ≤ ∑ _m∈range (J+1),(Fintype.card α*(N+1)+1)^J := by
      apply sum_le_sum
      intro m hm
      exact (Nat.pow_le_pow_left (Nat.le_succ _) m).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ (mem_range.mp hm)))
    _ = _ := by simp

variable {X : Type*} [Fintype X]

omit [Fintype α] [Fintype X] in
lemma sized_entries_le (S : Finset X) (U : α→Finset X) (bs : List α) :
    ∀ h∈GreedyPreparation.sized S U bs,h.2≤S.card := by
  induction bs generalizing S with
  | nil => simp [GreedyPreparation.sized]
  | cons b bs ih =>
    intro h hh
    rcases List.mem_cons.mp hh with rfl|hh
    · exact card_le_card inter_subset_left
    · exact (ih _ _ hh).trans (card_le_card sdiff_subset)

omit [Fintype X] in
lemma sized_header (S : Finset X) (U : α→Finset X) (bs : List α) (J N : ℕ)
    (hJ : bs.length≤J) (hN : S.card≤N) :
    GreedyPreparation.sized S U bs∈headers J N := by
  apply (mem_headers_iff _ _ _).mpr
  constructor
  · have hh := congrArg List.length (GreedyPreparation.sized_planes S U bs)
    simpa only [List.length_map] using hh.le.trans hJ
  · intro h hh
    exact (sized_entries_le S U bs h hh).trans hN

end
end SharpLogRamsey.DescriptionHeaders

end

end OAI
