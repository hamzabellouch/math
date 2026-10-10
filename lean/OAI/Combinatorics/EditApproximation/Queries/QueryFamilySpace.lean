import OAI.Combinatorics.EditApproximation.Queries.QueryScalarReadSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryRestrictionSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyActive

namespace OAI

namespace EditApproximation
open BitQuery

section Family
variable {α : Type*} {M J R : ℕ} [NeZero M] (source target : List α)
  (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (passes copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (time : Fin R)
  (q : TargetInterval target.length)

def queryFamilyRefinementHeap : Heap (queryFamilyRefinement source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta passes copies pass copy T S t ht node hbelow time q) :=
  queryPhysicalRandomDataRequestHeap source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta copies pass copy T S t ht node hbelow _ _ q
    (queryFamilyGroupReadHeap target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time)
    (queryFamilyOnlineReadHeap target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time)

end Family

section Active
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (request : PhysicalTableRequest M J target.length)
  (hindex : T < request.index) (hbelow : request.node.1.val < J)

def queryFamilyActiveHeap : Heap (queryFamilyActive (R := R) source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta T S passes copies request hindex hbelow) :=
  (queryFamilyRefinementHeap source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
    passes copies request.pass request.copy T S (request.index - T) (Nat.sub_pos_of_lt hindex)
    request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)

end Active

section Bounded
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)

def queryFamilyBoundedActiveHeap : Heap (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF
    hP hM hF tau a eta kappa delta T S passes copies parent hindex hbelow) :=
  queryRestrictPhysicalBodyHeap (passes + 1) copies T S parent _
    (queryFamilyActiveHeap (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies parent.val hindex hbelow)

end Bounded
end EditApproximation

end OAI
