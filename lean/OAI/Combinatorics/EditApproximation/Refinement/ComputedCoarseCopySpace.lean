import OAI.Combinatorics.EditApproximation.Coarse.CoarseInputStorage
import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialStorage
import OAI.Combinatorics.EditApproximation.Refinement.ComputedFreshWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter



theorem physicalCoarseInputStorage_polynomial {M J : ℕ} (source target : List ℕ) (N : ℕ)
    (hsize : source.length + target.length ≤ N)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3)
    (entry : PhysicalEntry M J target.length) :
    physicalCoarseInputStorage source target entry ≤ (N + 2) ^ 16 := by
  unfold physicalCoarseInputStorage
  exact coarsePreparedInputStorage_polynomial source target N
    (physicalSourceInterval source.length entry.1).lo
    (physicalSourceInterval source.length entry.1).hi entry.2.lo entry.2.hi
    (physicalSourceInterval source.length entry.1).ordered
    (physicalSourceInterval source.length entry.1).valid entry.2.ordered entry.2.valid hsize hsymbol



theorem computedFamilyCoarseCopyStorage_eq (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedFamilyCoarseCopyStorage source target N input =
      ((computedFamilyResult source target N input).freshKeys.map (coarseHistoryKeyCost
        (physicalCoarseInputStorage (M := (integerParameters N).M)
          (J := intervalTreeDepth (integerParameters N).M source.length) source target))).sum :=
  computedFamilyKernelWork_eq_fresh_sum source target N input _

theorem computedFamilyCoarseCopyStorage_bound (source target : List ℕ) (N : ℕ)
    (hsize : source.length + target.length ≤ N)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3)
    (input : ComputedFamilyInput source target N) :
    computedFamilyCoarseCopyStorage source target N input ≤
      (N + 2) ^ 16 * (computedFamilyResult source target N input).requests := by
  apply computedFamilyKernelWork_le
  apply coarseHistoryKeyCost_le
  intro entry
  exact physicalCoarseInputStorage_polynomial source target N hsize hsymbol entry

theorem computedFamilyCoarseCopyStorage_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ input : ComputedFamilyInput source target N,
      computedFamilyCoarseCopyStorage source target N input ≤ (N + 2) ^ 18 := by
  filter_upwards [computedFamilyResult_requests_near_linear 1 (by norm_num)] with N hr
  intro source target hsize hsymbol input
  have hrequests : (computedFamilyResult source target N input).requests ≤ (N + 2) ^ 2 := by
    have h := hr source target hsize input
    norm_num at h
    exact_mod_cast h
  calc
    _ ≤ (N + 2) ^ 16 * (computedFamilyResult source target N input).requests :=
      computedFamilyCoarseCopyStorage_bound source target N hsize hsymbol input
    _ ≤ (N + 2) ^ 16 * (N + 2) ^ 2 := Nat.mul_le_mul_left _ hrequests
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI
