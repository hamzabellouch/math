import OAI.Combinatorics.EditApproximation.Queries.QueryFamilySourceCosts
import OAI.Combinatorics.EditApproximation.Queries.QuerySourceKeyWidths

namespace OAI

namespace EditApproximation.BinaryFraction

def queryFamilySourceReadBudget (J B W : ℕ) : ℕ :=
  200 * (1000 * (B + 1) + 1000 + 2) ^ 2 + 120 * (B + 1) ^ 2 + 10 * J + 100 + W

end EditApproximation.BinaryFraction

namespace EditApproximation
section Family
variable {α : Type*} {M J R : ℕ} (target : List α)
  (N P F exponent H Q passes copies pass copy B W : ℕ)
  (oracle : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → BinaryFraction)
  (readWork : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → ℕ)
  (hN : Nat.size N ≤ B) (hp : Nat.size pass ≤ B) (hc : Nat.size copy ≤ B)
  (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
  (hW : ∀ key, readWork key ≤ W)

include hN hp hc hps hcs hW in
theorem queryFamilyGroupRead_bounded_work
    (hn : Nat.size target.length ≤ B) (he : exponent + 1 ≤ B)
    (node : PhysicalInternalNode M J) (time : Fin R) (key : GroupScalarKey M F Q)
    (hk : queryGroupKeySize key ≤ 40 * B + 500) :
    (queryFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key).work oracle readWork ≤
      BinaryFraction.queryFamilySourceReadBudget J B W := by
  let D := 1000 * (B + 1) + 1000
  let K := 120 * (B + 1) ^ 2 + 5 * J + 55
  have hb : B ≤ D := by dsimp only [D]; omega
  have hkey : queryGroupKeySize key ≤ D := by dsimp only [D]; omega
  have hscale := queryScalePresentWithWork_cost N key.1.1 D (hN.trans hb)
    (by unfold queryGroupKeySize at hkey; omega)
  have hcell := queryCellValidWithWork_cost target.length exponent D key.1.2
    (hn.trans hb) (he.trans hb) (by unfold queryGroupKeySize at hkey; omega)
    (by unfold queryGroupKeySize at hkey; omega)
  have hr := queryFamilyGroupRead_work target N P F exponent H Q passes copies pass copy oracle readWork K W
    (fun scalar => queryFamilyTagWithWork_cost target N P F exponent H Q passes copies pass copy B hp hc hps hcs scalar)
    hW node time key
  change _ ≤ 200 * (D + 2) ^ 2 + 120 * (B + 1) ^ 2 + 10 * J + 100 + W
  dsimp only [K] at hr
  nlinarith only [hscale, hcell, hr, Nat.zero_le D]

include hN hp hc hps hcs hW in
theorem queryFamilyOnlineRead_bounded_work
    (hbound : Nat.size (localOnlineMassBound M P H) ≤ B)
    (node : PhysicalInternalNode M J) (time : Fin R) (key : ℕ × TargetInterval target.length)
    (range : ℕ) (hk : Nat.size key.1 ≤ B + 1) (hrange : Nat.size range ≤ 240 * (B + 5) + 7) :
    (queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range).work oracle readWork ≤
      BinaryFraction.queryFamilySourceReadBudget J B W := by
  let D := 1000 * (B + 1) + 1000
  let K := 120 * (B + 1) ^ 2 + 5 * J + 55
  have hb : B ≤ D := by dsimp only [D]; omega
  have hs := queryScalePresentWithWork_cost N key.1 D (hN.trans hb) (by dsimp only [D]; omega)
  have hv := queryRangeValidWithWork_cost (localOnlineMassBound M P H) range D
    (hbound.trans hb) (by dsimp only [D]; omega)
  have hr := queryFamilyOnlineRead_work target N P F exponent H Q passes copies pass copy oracle readWork K W
    (fun scalar => queryFamilyTagWithWork_cost target N P F exponent H Q passes copies pass copy B hp hc hps hcs scalar)
    hW node time key range
  change _ ≤ 200 * (D + 2) ^ 2 + 120 * (B + 1) ^ 2 + 10 * J + 100 + W
  dsimp only [K] at hr
  nlinarith only [hs, hv, hr, Nat.zero_le D]

end Family
end EditApproximation

end OAI
