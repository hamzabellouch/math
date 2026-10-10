import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalProgram
import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyScalarReads

namespace OAI

/-! The charged local refinement uses the independent source
family, with computed scalar guards and pass/copy addresses. -/

namespace EditApproximation

section Family
variable {α : Type*} {M J R : ℕ} [NeZero M] (source target : List α)
  (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (passes copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (time : Fin R)
  (q : TargetInterval target.length)

def queryFamilyRefinement :
    BitQuery (Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)
      {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
        (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S}) BinaryFraction :=
  queryPhysicalRandomDataRequest source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta copies pass copy T S t ht node hbelow
    (queryFamilyGroupRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time)
    (queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time) q

theorem queryFamilyRefinement_refines :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyRefinement source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
        passes copies pass copy T S t ht node hbelow time q)
      (physicalRandomDataRequestQuery source target N P F exponent H Q tau.value a.value eta.value
        kappa.value delta.value pass copy T S t ht node hbelow
        (physicalFamilyGroupRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time)
        (physicalFamilyOnlineRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time) q) := by
  apply queryPhysicalRandomDataRequest_refines
  · intro key
    exact queryFamilyGroupRead_refines target N P F exponent H Q passes copies pass copy _ time key
  · intro key range
    exact queryFamilyOnlineRead_refines target N P F exponent H Q passes copies pass copy _ time key range

end Family
end EditApproximation

end OAI
