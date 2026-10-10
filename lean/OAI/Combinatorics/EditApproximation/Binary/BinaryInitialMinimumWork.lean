import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialWork

namespace OAI

/-! The initial entry's complete arithmetic counter, including its zero
test, spatial coefficient, fallback and finite minimum. Grid construction
is charged by the separate local endpoint enumerator. -/

namespace EditApproximation
namespace BinaryFraction

def initialMinimumInputBudget (B : ℕ) : ℕ := 40 * B + 22

def initialMinimumWordBudget (B : ℕ) : ℕ :=
  128 * B + 90 + initialConeWordBudget (initialMinimumInputBudget B)

def initialMinimumBitBudget (n B : ℕ) : ℕ :=
  (8 * B + 2) + 2000 * (B + 1) ^ 2 + 6000 * (4 * B + 3) ^ 2 +
    2000 * (32 * B + 23) ^ 2 + n * (initialConeBitBudget (initialMinimumInputBudget B) + 3) +
    (1 + n * (1000 * (initialMinimumWordBudget B + 1) ^ 2 + 2)) + 2 * B + 6

theorem initialMinimumWithWork_bounds {n : ℕ} (sourceLength : ℕ) (U : TargetInterval n → ℕ)
    (N F : ℕ) (a : BinaryFraction) (query : TargetInterval n) (centers : List (TargetInterval n))
    (B : ℕ) (hB : 8 ≤ B) (hs : Nat.size sourceLength + 2 ≤ B)
    (hUq : Nat.size (U query) ≤ B) (hN : Nat.size N + 2 ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hql : Nat.size query.lo + 2 ≤ B) (hqh : Nat.size query.hi + 2 ≤ B)
    (hcenters : ∀ center ∈ centers, Nat.size (U center) + 2 ≤ B ∧
      Nat.size center.lo + 2 ≤ B ∧ Nat.size center.hi + 2 ≤ B) :
    (initialMinimumWithWork sourceLength U N F a query centers).1.width ≤ initialMinimumWordBudget B ∧
      (initialMinimumWithWork sourceLength U N F a query centers).2 ≤
        initialMinimumBitBudget centers.length B := by
  let L := canonicalMulWithWork (nat 32) (nat F)
  let coefficient := canonicalAddWithWork L.1 one
  let fallback := canonicalMulWithWork coefficient.1 (nat N)
  let W := initialMinimumInputBudget B
  have hW : B ≤ W := by dsimp only [W, initialMinimumInputBudget]; omega
  have h32 : (nat 32).width ≤ B := by
    have h : (nat 32).width ≤ 8 := by decide
    omega
  have hFw := (nat_width_le F).trans hF
  have hNw := (nat_width_le N).trans hN
  have hL := canonicalMulWithWork_width (nat 32) (nat F) B h32 hFw
  have hLc := canonicalMulWithWork_cost (nat 32) (nat F) B h32 hFw
  have hcoef := canonicalAddWithWork_width L.1 one (4 * B + 2) hL (by change 1 ≤ _; omega)
  have hcoefc := canonicalAddWithWork_cost L.1 one (4 * B + 2) hL (by change 1 ≤ _; omega)
  have hcoefBound : coefficient.1.width ≤ 32 * B + 22 := by
    change coefficient.1.width ≤ _ at hcoef
    omega
  have hfall := canonicalMulWithWork_width coefficient.1 (nat N) (32 * B + 22) hcoefBound (by omega)
  have hfallc := canonicalMulWithWork_cost coefficient.1 (nat N) (32 * B + 22) hcoefBound (by omega)
  have hscore (center : TargetInterval n) (hc : center ∈ centers) :=
    initialConeWithWork_bounds sourceLength U a L.1 query center W (by omega)
      (hs.trans hW) ((hcenters center hc).1.trans hW) (ha.trans hW) (hL.trans (by
        dsimp only [W, initialMinimumInputBudget]; omega))
      (hql.trans hW) (hqh.trans hW) ((hcenters center hc).2.1.trans hW)
      ((hcenters center hc).2.2.trans hW)
  let scores := arithmeticMapWithWork (initialConeWithWork sourceLength U a L.1 query) centers
  have hscoreWidths : ∀ score ∈ scores.1, score.width ≤ initialMinimumWordBudget B := by
    intro score hscore'
    simp only [scores, arithmeticMapWithWork_value] at hscore'
    obtain ⟨center, hc, rfl⟩ := List.mem_map.mp hscore'
    exact (hscore center hc).1.trans (by
      change initialConeWordBudget (initialMinimumInputBudget B) ≤ _
      unfold initialMinimumWordBudget
      omega)
  have hfallWidth : fallback.1.width ≤ initialMinimumWordBudget B := hfall.trans (by
    unfold initialMinimumWordBudget; omega)
  have hscoreCost := arithmeticMapWithWork_cost (initialConeWithWork sourceLength U a L.1 query)
    centers (initialConeBitBudget W) (fun center hc => (hscore center hc).2)
  have hmin := minimumWithWork_width fallback.1 scores.1 (initialMinimumWordBudget B)
    hfallWidth hscoreWidths
  have hminCost := minimumWithWork_cost fallback.1 scores.1 (initialMinimumWordBudget B)
    hfallWidth hscoreWidths
  have hlen : scores.1.length = centers.length := by
    simp only [scores, arithmeticMapWithWork_value, List.length_map]
  rw [hlen] at hminCost
  have hz := naturalEqualWithWork_cost (U query) 0 B hUq (by simp)
  unfold initialMinimumWithWork
  dsimp only
  split_ifs with hzero
  · constructor
    · have hwidth : zero.width = 1 := rfl
      change zero.width ≤ _
      rw [hwidth]
      unfold initialMinimumWordBudget
      omega
    · change (naturalEqualWithWork (U query) 0).2 + 1 ≤ _
      unfold initialMinimumBitBudget
      omega
  · refine ⟨hmin, ?_⟩
    change (naturalEqualWithWork (U query) 0).2 + L.2 + coefficient.2 + fallback.2 +
      scores.2 + (minimumWithWork fallback.1 scores.1).2 + Nat.size F + Nat.size N + 6 ≤ _
    change scores.2 ≤ centers.length * (initialConeBitBudget (initialMinimumInputBudget B) + 3) at hscoreCost
    change L.2 ≤ _ at hLc
    change coefficient.2 ≤ _ at hcoefc
    change fallback.2 ≤ _ at hfallc
    simp only [Nat.add_assoc, Nat.reduceAdd] at hcoefc hfallc
    unfold initialMinimumBitBudget
    omega

end BinaryFraction
end EditApproximation

end OAI
