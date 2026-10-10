import OAI.Combinatorics.BalancedRyser.Candidates.CandidateAsymptotics
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateGraphReduction

namespace OAI

open Filter
open scoped Topology

namespace Balanced.CandidateAsymptotics

theorem eventually_scaled_candidate_numerics (a : ℕ) (ha : 1 ≤ a) :
    ∀ᶠ q : ℕ in atTop,
    let P := a * Nat.ceil ((q : ℝ) ^ (1 / 100 : ℝ))
    let B := Nat.ceil (Real.log (q : ℝ))
    let R := 6 * P + 16 * B * P
    (((2 + 4 * P : ℕ) : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
    (((4 + P + R : ℕ) : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
    (((48 + 10 * P + 2 * R : ℕ) : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
    (((8 * (q + 1) + R : ℕ) : ℝ) ≤ 10 * q) := by
  have hsmall := eventually_scaled_product_le (102 * (a : ℝ))
  have hlogone : ∀ᶠ q : ℕ in atTop, 1 ≤ Real.log (q : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hsmall, hlogone, eventually_ge_atTop 8] with q hsmall hlog hq
  dsimp only
  let P : ℝ := (a : ℝ) * Nat.ceil ((q : ℝ) ^ (1 / 100 : ℝ))
  let B : ℝ := Nat.ceil (Real.log (q : ℝ))
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hceil : (1 : ℝ) ≤ Nat.ceil ((q : ℝ) ^ (1 / 100 : ℝ)) :=
    (Real.one_le_rpow hqone (by norm_num : (0 : ℝ) ≤ 1 / 100)).trans (Nat.le_ceil _)
  have hP : 1 ≤ P := by dsimp [P]; nlinarith
  have hB : 1 ≤ B := hlog.trans (Nat.le_ceil _)
  have hBP : 1 ≤ B * P := by nlinarith
  have hPBP : P ≤ B * P := by nlinarith
  have hbig : 102 * (B * P) ≤ (q : ℝ) ^ (1 / 8 : ℝ) := by
    dsimp [P, B]
    nlinarith [hsmall]
  have hpowq : (q : ℝ) ^ (1 / 8 : ℝ) ≤ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hqone
      (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hq8 : (8 : ℝ) ≤ q := by exact_mod_cast hq
  push_cast
  change (2 + 4 * P ≤ _) ∧ (4 + P + (6 * P + 16 * B * P) ≤ _) ∧
    (48 + 10 * P + 2 * (6 * P + 16 * B * P) ≤ _) ∧
    (8 * ((q : ℝ) + 1) + (6 * P + 16 * B * P) ≤ _)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

end Balanced.CandidateAsymptotics

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical
universe u

theorem exists_threshold_candidateGraphGood_of_scaled_counts
    (a : ℕ) (ha : 1 ≤ a) (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F → ∀ (M : MergedPairs F) (c : ℝ),
      let P := a * Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ))
      (∀ s : Slot F, c * Fintype.card F ≤ ((candidateSlot M s).card : ℝ)) →
      (∀ p, (pointCandidates M p).card ≤ P) →
      (∀ p l, ¬ OnLine p l → (pointLineCandidates M p l).card ≤ P) →
      (∀ l k : Line F, l ≠ k → l ∉ constituentLines M → k ∉ constituentLines M →
        (twoLineCandidates M l k).card ≤ P) →
      (∀ e : Finset (Direction F), e.card = 2 → (generatorPairCandidates M e).card ≤ P) →
      (∀ p, sampledMultiplicity M p ≤ Nat.ceil (Real.log (Fintype.card F : ℝ))) →
      (∀ s : Slot F, ∀ l : Line F, (lineHitSlot M s l).card ≤ P) →
      (∀ l : Line F, l ∉ constituentLines M →
        (((candidateVertices M).filter (fun w => ∃ p ∈ points M w, OnLine p l)).card : ℝ) ≤
          C * Fintype.card F) →
      (∀ l : Line F, l ∉ initialDeletedLines M →
        (1 / 5 : ℝ) * Fintype.card F ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ)) →
      CandidateGraphGood M c (C + 11) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((CandidateAsymptotics.eventually_scaled_candidate_numerics a ha).and
      (eventually_ge_atTop 1))
  refine ⟨N, ?_⟩
  intro F _ _ _ hq M c P hsize hpoint hmixed htwo hpair hcap hline hglobal hoccupancy
  obtain ⟨hnum, hqone⟩ := hN (Fintype.card F) hq
  let B := Nat.ceil (Real.log (Fintype.card F : ℝ))
  let D := Nat.ceil (C * (Fintype.card F : ℝ))
  apply candidateGraphGood_of_counts M c (C + 11) P P B D
    hsize hpoint hmixed htwo hpair hcap le_rfl hline
  · intro l hl
    exact_mod_cast (hglobal l hl).trans (Nat.le_ceil _)
  · have hD : (D : ℝ) < C * (Fintype.card F : ℝ) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hC (Nat.cast_nonneg _))
    have hqreal : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast hqone
    have hn := hnum.2.2.2
    change (((8 * (Fintype.card F + 1) + (6 * P + 16 * B * P) : ℕ) : ℝ)) ≤
      10 * (Fintype.card F : ℝ) at hn
    push_cast at hn ⊢
    nlinarith
  · exact hnum.2.1
  · exact hnum.1
  · exact hnum.2.2.1
  · exact hoccupancy

end
end Balanced.CandidateIncidence

end OAI
