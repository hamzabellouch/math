import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedControlSpace
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedInitial
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarsePolynomial

namespace OAI

namespace EditApproximation

namespace BinaryFraction

def coarseIndexedRootInvocations {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d) : ℕ :=
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := coarseGridNatWithWork den.1 denPos 2
  let allowance := coarseGridNatWithWork den.1 denPos k
  coarseDenominatorInvocations (1 : ℕ).bits q.bits L.bits B.bits d +
    coarseGridNatInvocations den.1 denPos 2 + coarseGridNatInvocations den.1 denPos k +
    coarseIndexedInvocations k q L (coarseEntryWidth x y) x y two.1 d 0 draws allowance.1 0 + 1

theorem coarseIndexedRootInvocations_le_work {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d) :
    coarseIndexedRootInvocations k q L hB hq hL x y draws ≤
      2 * (coarseIndexedRootWithWork k q L hB hq hL x y draws).2 := by
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  have hd := coarseDenominatorInvocations_le_work (1 : ℕ).bits q.bits L.bits B.bits d
  have ht := coarseGridNatInvocations_le_work den.1 denPos 2
  have ha := coarseGridNatInvocations_le_work den.1 denPos k
  have he := coarseIndexedInvocations_le_work k q L (coarseEntryWidth x y) x y
    (coarseGridNatWithWork den.1 denPos 2).1 d 0 draws
    (coarseGridNatWithWork den.1 denPos k).1 0
  change coarseDenominatorInvocations (1 : ℕ).bits q.bits L.bits B.bits d ≤ den.2 at hd
  unfold coarseIndexedRootInvocations coarseIndexedRootWithWork
  change coarseDenominatorInvocations (1 : ℕ).bits q.bits L.bits B.bits d +
    coarseGridNatInvocations den.1 denPos 2 + coarseGridNatInvocations den.1 denPos k +
    coarseIndexedInvocations k q L (coarseEntryWidth x y) x y
      (coarseGridNatWithWork den.1 denPos 2).1 d 0 draws
      (coarseGridNatWithWork den.1 denPos k).1 0 + 1 ≤
    2 * (den.2 + (coarseGridNatWithWork den.1 denPos 2).2 +
      (coarseGridNatWithWork den.1 denPos k).2 +
      (coarseIndexedWithWork k q L (coarseEntryWidth x y) x y
        (coarseGridNatWithWork den.1 denPos 2).1 d 0 draws
        (coarseGridNatWithWork den.1 denPos k).1 0).2 + 1)
  omega

def coarseIndexedCandidateInvocations {B d : ℕ} (q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d) : ℕ :=
  let k := coarseGuess (coarseEntryWidth x y) i
  let root := coarseIndexedRootWithWork k q L hB hq hL x y draws
  let shifted := canonicalAddWithWork root.1 (nat k)
  coarseIndexedRootInvocations k q L hB hq hL x y draws +
    canonicalAddInvocations root.1 (nat k) + canonicalMulInvocations (nat 2) shifted.1 + 1

theorem coarseIndexedCandidateInvocations_le_work {B d : ℕ} (q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d) :
    coarseIndexedCandidateInvocations q L hB hq hL x y i draws ≤
      2 * (coarseIndexedCandidateWithWork q L hB hq hL x y i draws).2 := by
  let k := coarseGuess (coarseEntryWidth x y) i
  let root := coarseIndexedRootWithWork k q L hB hq hL x y draws
  have hr := coarseIndexedRootInvocations_le_work k q L hB hq hL x y draws
  have ha := canonicalAddInvocations_le_work root.1 (nat k)
  have hm := canonicalMulInvocations_le_work (nat 2) (canonicalAddWithWork root.1 (nat k)).1
  change coarseIndexedRootInvocations k q L hB hq hL x y draws +
    canonicalAddInvocations root.1 (nat k) +
    canonicalMulInvocations (nat 2) (canonicalAddWithWork root.1 (nat k)).1 + 1 ≤
    2 * (root.2 + (canonicalAddWithWork root.1 (nat k)).2 +
      (canonicalMulWithWork (nat 2) (canonicalAddWithWork root.1 (nat k)).1).2 + Nat.size k + 3)
  change coarseIndexedRootInvocations k q L hB hq hL x y draws ≤ 2 * root.2 at hr
  omega

def coarseMinimumListInvocations (fallback : BinaryFraction) : List BinaryFraction → ℕ
  | [] => 1
  | head :: rest => coarseMinimumListInvocations fallback rest + compareInvocations head (minimumWithWork fallback rest).1 + 2

theorem coarseMinimumListInvocations_le_work (fallback : BinaryFraction) (values : List BinaryFraction) :
    coarseMinimumListInvocations fallback values ≤ (minimumWithWork fallback values).2 := by
  induction values with
  | nil => exact Nat.le_refl 1
  | cons head rest ih =>
    have h := compareInvocations_le_work head (minimumWithWork fallback rest).1
    simp only [coarseMinimumListInvocations, minimumWithWork, minWithWork]
    omega

def coarseMinimumInvocations : List BinaryFraction → ℕ
  | [] => 1
  | a :: rest => coarseMinimumListInvocations a rest + 1

theorem coarseMinimumInvocations_le_work (values : List BinaryFraction) :
    coarseMinimumInvocations values ≤ 2 * (coarseMinimumWithWork values).2 := by
  cases values with
  | nil => exact (by decide : 1 ≤ 2)
  | cons a rest =>
    have h := coarseMinimumListInvocations_le_work a rest
    have hp : 1 ≤ (minimumWithWork a rest).2 := by
      cases rest <;> simp only [minimumWithWork] <;> omega
    change coarseMinimumListInvocations a rest + 1 ≤ 2 * (minimumWithWork a rest).2
    omega


def naturalListEqualInvocations : List ℕ → List ℕ → ℕ
  | [], [] => 1
  | a :: left, b :: right =>
    bitCompareInvocations a.bits b.bits + 2 +
      if (naturalEqualWithWork a b).1 then naturalListEqualInvocations left right else 0
  | _, _ => 1

theorem naturalListEqualInvocations_le_work (x y : List ℕ) :
    naturalListEqualInvocations x y ≤ (naturalListEqualWithWork x y).2 := by
  induction x generalizing y with
  | nil => cases y <;> exact Nat.le_refl 1
  | cons a left ih =>
    cases y with
    | nil => exact Nat.le_refl 1
    | cons b right =>
      have ht := ih right
      have hc := bitCompareInvocations_le_work a.bits b.bits
      simp only [naturalListEqualInvocations, naturalListEqualWithWork]
      split_ifs <;> simp only [naturalEqualWithWork, binaryNaturalCompareWithWork] <;> omega

def coarseIndexedInitialInvocations {B d : ℕ} (q L N : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) : ℕ :=
  let long := binaryNaturalCompareWithWork (2 * x.length) y.length
  let longCalls := bitCompareInvocations (2 * x.length).bits y.length.bits
  if long.1 = .lt then longCalls + 1 else
  let equal := naturalListEqualWithWork x y
  if equal.1 then longCalls + naturalListEqualInvocations x y + 1 else
  let indices := List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)
  let roots := arithmeticMapWithWork (fun i => coarseIndexedCandidateWithWork q L hB hq hL x y i (draws i)) indices
  let smallest := coarseMinimumWithWork roots.1
  let rounded := naturalCeilingWithWork smallest.1
  longCalls + naturalListEqualInvocations x y +
    arithmeticMapInvocations (fun i => coarseIndexedCandidateInvocations q L hB hq hL x y i (draws i)) indices +
    indices.length + 1 + coarseMinimumInvocations roots.1 + naturalCeilingInvocations smallest.1 +
    bitCompareInvocations rounded.1 N.bits + 3

theorem coarseIndexedInitialInvocations_le_work {B d : ℕ} (q L N : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) :
    coarseIndexedInitialInvocations q L N hB hq hL x y draws ≤
      2 * (coarseIndexedInitialWithWork q L N hB hq hL x y draws).2 := by
  let indices := List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)
  let roots := arithmeticMapWithWork (fun i => coarseIndexedCandidateWithWork q L hB hq hL x y i (draws i)) indices
  have hr := arithmeticMapInvocations_with_indices_le_work
    (fun i => coarseIndexedCandidateWithWork q L hB hq hL x y i (draws i))
    (fun i => coarseIndexedCandidateInvocations q L hB hq hL x y i (draws i)) indices
    (fun i _ => (coarseIndexedCandidateInvocations_le_work q L hB hq hL x y i (draws i)).trans (Nat.le_succ _))
  have hm := coarseMinimumInvocations_le_work roots.1
  have hc := naturalCeilingInvocations_le_work (coarseMinimumWithWork roots.1).1
  have hl := bitCompareInvocations_le_work (2 * x.length).bits y.length.bits
  have he := naturalListEqualInvocations_le_work x y
  have hf := bitCompareInvocations_le_work
    (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).1 N.bits
  unfold coarseIndexedInitialInvocations coarseIndexedInitialWithWork
  dsimp only
  split_ifs
  · simp only [binaryNaturalCompareWithWork] at *
    omega
  · simp only [binaryNaturalCompareWithWork] at *
    omega
  · change bitCompareInvocations (2 * x.length).bits y.length.bits + naturalListEqualInvocations x y +
        arithmeticMapInvocations
          (fun i => coarseIndexedCandidateInvocations q L hB hq hL x y i (draws i)) indices +
        indices.length + 1 + coarseMinimumInvocations roots.1 +
        naturalCeilingInvocations (coarseMinimumWithWork roots.1).1 +
        bitCompareInvocations (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).1 N.bits + 3 ≤
      2 * ((binaryNaturalCompareWithWork (2 * x.length) y.length).2 +
        (naturalListEqualWithWork x y).2 + roots.2 + (coarseMinimumWithWork roots.1).2 +
        (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).2 +
        (wordMinWithWork N.bits (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).1).2 + Nat.size N + 6)
    change arithmeticMapInvocations
      (fun i => coarseIndexedCandidateInvocations q L hB hq hL x y i (draws i)) indices +
      indices.length + 1 ≤ 2 * roots.2 + 2 at hr
    simp only [binaryNaturalCompareWithWork, wordMinWithWork, wordLEWithWork]
    omega

open Filter in
theorem computedCoarseIndexedInitialInvocations_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      coarseIndexedInitialInvocations (inputHeight N ^ 4) (64 * inputHeight N) N
        hB hq hL x y draws ≤ (N + 2) ^ 181 := by
  filter_upwards [computedCoarseIndexedInitialWithWork_polynomial] with N hN
  intro B d x y hBdef hddef hsize hsymbols hB hq hL draws
  have hw := hN B d x y hBdef hddef hsize hsymbols hB hq hL draws
  have ha := coarseIndexedInitialInvocations_le_work (inputHeight N ^ 4) (64 * inputHeight N) N hB hq hL x y draws
  calc
    _ ≤ 2 * (N + 2) ^ 180 := ha.trans (Nat.mul_le_mul_left 2 hw)
    _ ≤ (N + 2) * (N + 2) ^ 180 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := (pow_succ' (N + 2) 180).symm

end BinaryFraction
end EditApproximation

end OAI
