import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyRefinement
import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalProgramCost
import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyReaderBounds

namespace OAI

namespace EditApproximation
section Family
variable {α : Type*} {M J R : ℕ} [NeZero M] (source target : List α)
  (N P F exponent H Q eM eF B E Scale : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (passes copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (time : Fin R) (q : TargetInterval target.length)
  (oracle : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
    {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
      (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)
  (readWork : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
    {child : PhysicalTableRequest M J target.length // child.combinedRank T S <
      (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → ℕ)

local notation "tableOracle" => (fun key => oracle (Sum.inr key))
open BinaryFraction

theorem queryFamilyRefinement_work_bound (V C : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E Scale (t - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hV : 2 ≤ V) (hVB : V ≤ B) (hMean : warmupAverageWordBudget T V ≤ B)
    (hc : ∀ key, key.val.pass = pass → key.val.copy = copy → readWork (Sum.inr key) ≤ C)
    (hs : ∀ key, readWork (Sum.inl key) ≤ C)
    (hv : ∀ key, (tableOracle key).width ≤ V)
    (hsv : ∀ key, (oracle (Sum.inl key)).width ≤ B)
    (hnonneg : ∀ key, 0 ≤ (tableOracle key).value)
    (hprior : ∀ input : Fin M × ℕ × TargetInterval target.length,
      ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value tableOracle).value ≤
        ((queryPhysicalWarmupRead copies pass copy T S t ht node q
          (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
          0 (Nat.zero_le T) input.2.2).value tableOracle).value)
    (hp : Nat.size pass ≤ B) (hcopy : Nat.size copy ≤ B)
    (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
    (hbound : Nat.size (localOnlineMassBound M P H) ≤ B) :
    (queryFamilyRefinement source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
      passes copies pass copy T S t ht node hbelow time q).work oracle readWork ≤
      queryLocalProgramBitBudget M N P F exponent eM eF B Scale t
        (queryPhysicalDataBudget T J B V C (queryFamilySourceReadBudget J B (C + 1))) := by
  have hB : 2 ≤ B := by have := hn.largeBits; omega
  have htarget : Nat.size target.length ≤ B := by have := hn.targetSize; omega
  unfold queryFamilyRefinement
  apply queryPhysicalRandomDataRequest_work_bound source target N P F exponent H Q eM eF B E Scale
    hP hM hF tau a eta kappa delta copies pass copy T S t ht node hbelow _ _ q oracle readWork
    V C (queryFamilySourceReadBudget J B (C + 1)) hn htime hPd hV hVB hMean hc hv hnonneg hprior
  · intro key
    exact queryFamilyGroupRead_width target N P F exponent H Q passes copies pass copy B
      (fun key => oracle (Sum.inl key)) hB hsv ⟨node, hbelow⟩ time key
  · intro key range
    exact queryFamilyOnlineRead_width target N P F exponent H Q passes copies pass copy B
      (fun key => oracle (Sum.inl key)) hB hsv ⟨node, hbelow⟩ time key range
  · intro key hk
    exact queryFamilyGroupRead_bounded_work target N P F exponent H Q passes copies pass copy B (C + 1)
      (fun key => oracle (Sum.inl key)) (fun key => 1 + readWork (Sum.inl key))
      hn.inputSize hp hcopy hps hcs (fun key => by have := hs key; omega)
      htarget hn.thetaSize ⟨node, hbelow⟩ time key hk
  · intro key range hk hr
    exact queryFamilyOnlineRead_bounded_work target N P F exponent H Q passes copies pass copy B (C + 1)
      (fun key => oracle (Sum.inl key)) (fun key => 1 + readWork (Sum.inl key))
      hn.inputSize hp hcopy hps hcs (fun key => by have := hs key; omega)
      hbound ⟨node, hbelow⟩ time key range hk hr

end Family
end EditApproximation

end OAI
