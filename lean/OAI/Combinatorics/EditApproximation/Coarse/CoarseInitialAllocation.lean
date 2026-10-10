import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedAllocation
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedInitial
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarsePolynomial

namespace OAI

namespace EditApproximation

/-- Besides each result cell, reserve one index-list cell for each callback. -/
theorem arithmeticMapAllocation_with_indices_le_work {α β : Type*} (f : α → β × ℕ)
    (allocation : α → ℕ) (values : List α)
    (h : ∀ a ∈ values, allocation a ≤ 2 * (f a).2) :
    arithmeticMapAllocation allocation values + values.length ≤
      2 * (arithmeticMapWithWork f values).2 := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    have hh := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [arithmeticMapAllocation, arithmeticMapWithWork, List.length_cons]
    omega

namespace BinaryFraction

def coarseIndexedRootAllocation {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d) : ℕ :=
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := coarseGridNatWithWork den.1 denPos 2
  let allowance := coarseGridNatWithWork den.1 denPos k
  coarseDenominatorAllocation (1 : ℕ).bits q.bits L.bits B.bits d +
    coarseGridNatAllocation den.1 denPos 2 + coarseGridNatAllocation den.1 denPos k +
    coarseIndexedAllocation k q L (coarseEntryWidth x y) x y two.1 d 0 draws allowance.1 0

theorem coarseIndexedRootAllocation_le_work {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d) :
    coarseIndexedRootAllocation k q L hB hq hL x y draws ≤
      2 * (coarseIndexedRootWithWork k q L hB hq hL x y draws).2 := by
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  have hd := coarseDenominatorAllocation_le_work (1 : ℕ).bits q.bits L.bits B.bits d
  have ht := coarseGridNatAllocation_le_work den.1 denPos 2
  have ha := coarseGridNatAllocation_le_work den.1 denPos k
  have he := coarseIndexedAllocation_le_work k q L (coarseEntryWidth x y) x y
    (coarseGridNatWithWork den.1 denPos 2).1 d 0 draws
    (coarseGridNatWithWork den.1 denPos k).1 0
  change coarseDenominatorAllocation (1 : ℕ).bits q.bits L.bits B.bits d ≤ den.2 at hd
  unfold coarseIndexedRootAllocation coarseIndexedRootWithWork
  change coarseDenominatorAllocation (1 : ℕ).bits q.bits L.bits B.bits d +
    coarseGridNatAllocation den.1 denPos 2 + coarseGridNatAllocation den.1 denPos k +
    coarseIndexedAllocation k q L (coarseEntryWidth x y) x y
      (coarseGridNatWithWork den.1 denPos 2).1 d 0 draws
      (coarseGridNatWithWork den.1 denPos k).1 0 ≤
    2 * (den.2 + (coarseGridNatWithWork den.1 denPos 2).2 +
      (coarseGridNatWithWork den.1 denPos k).2 +
      (coarseIndexedWithWork k q L (coarseEntryWidth x y) x y
        (coarseGridNatWithWork den.1 denPos 2).1 d 0 draws
        (coarseGridNatWithWork den.1 denPos k).1 0).2 + 1)
  omega

def coarseIndexedCandidateAllocation {B d : ℕ} (q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d) : ℕ :=
  let k := coarseGuess (coarseEntryWidth x y) i
  let root := coarseIndexedRootWithWork k q L hB hq hL x y draws
  let shifted := canonicalAddWithWork root.1 (nat k)
  coarseIndexedRootAllocation k q L hB hq hL x y draws +
    canonicalAddAllocation root.1 (nat k) + canonicalMulAllocation (nat 2) shifted.1 + Nat.size k

theorem coarseIndexedCandidateAllocation_le_work {B d : ℕ} (q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d) :
    coarseIndexedCandidateAllocation q L hB hq hL x y i draws ≤
      2 * (coarseIndexedCandidateWithWork q L hB hq hL x y i draws).2 := by
  let k := coarseGuess (coarseEntryWidth x y) i
  let root := coarseIndexedRootWithWork k q L hB hq hL x y draws
  have hr := coarseIndexedRootAllocation_le_work k q L hB hq hL x y draws
  have ha := canonicalAddAllocation_le_work root.1 (nat k)
  have hm := canonicalMulAllocation_le_work (nat 2) (canonicalAddWithWork root.1 (nat k)).1
  change coarseIndexedRootAllocation k q L hB hq hL x y draws +
    canonicalAddAllocation root.1 (nat k) +
    canonicalMulAllocation (nat 2) (canonicalAddWithWork root.1 (nat k)).1 + Nat.size k ≤
    2 * (root.2 + (canonicalAddWithWork root.1 (nat k)).2 +
      (canonicalMulWithWork (nat 2) (canonicalAddWithWork root.1 (nat k)).1).2 + Nat.size k + 3)
  change coarseIndexedRootAllocation k q L hB hq hL x y draws ≤ 2 * root.2 at hr
  omega

def coarseMinimumListAllocation (fallback : BinaryFraction) : List BinaryFraction → ℕ
  | [] => 0
  | head :: rest => coarseMinimumListAllocation fallback rest + head.ltAllocation (minimumWithWork fallback rest).1

theorem coarseMinimumListAllocation_le_work (fallback : BinaryFraction) (values : List BinaryFraction) :
    coarseMinimumListAllocation fallback values ≤ (minimumWithWork fallback values).2 := by
  induction values with
  | nil => exact Nat.zero_le _
  | cons head rest ih =>
    have h := ltAllocation_le_work head (minimumWithWork fallback rest).1
    simp only [coarseMinimumListAllocation, minimumWithWork, minWithWork]
    omega

def coarseMinimumAllocation : List BinaryFraction → ℕ
  | [] => 0
  | a :: rest => coarseMinimumListAllocation a rest

theorem coarseMinimumAllocation_le_work (values : List BinaryFraction) :
    coarseMinimumAllocation values ≤ (coarseMinimumWithWork values).2 := by
  cases values with
  | nil => exact Nat.zero_le _
  | cons a rest => exact coarseMinimumListAllocation_le_work a rest

/-- Fresh arithmetic cells and root/index list spines. Constant words and
preexisting input/cached words are shared. The retained input and output
words are counted separately by the global storage capacity. -/
def coarseIndexedInitialAllocation {B d : ℕ} (q L N : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) : ℕ :=
  let long := binaryNaturalCompareWithWork (2 * x.length) y.length
  if long.1 = .lt then 0 else
  let equal := naturalListEqualWithWork x y
  if equal.1 then 0 else
  let indices := List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)
  let roots := arithmeticMapWithWork (fun i => coarseIndexedCandidateWithWork q L hB hq hL x y i (draws i)) indices
  let smallest := coarseMinimumWithWork roots.1
  arithmeticMapAllocation (fun i => coarseIndexedCandidateAllocation q L hB hq hL x y i (draws i)) indices +
    indices.length + coarseMinimumAllocation roots.1 + naturalCeilingAllocation smallest.1 + Nat.size N

theorem coarseIndexedInitialAllocation_le_work {B d : ℕ} (q L N : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) :
    coarseIndexedInitialAllocation q L N hB hq hL x y draws ≤
      2 * (coarseIndexedInitialWithWork q L N hB hq hL x y draws).2 := by
  let indices := List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)
  let roots := arithmeticMapWithWork (fun i => coarseIndexedCandidateWithWork q L hB hq hL x y i (draws i)) indices
  have hr := arithmeticMapAllocation_with_indices_le_work
    (fun i => coarseIndexedCandidateWithWork q L hB hq hL x y i (draws i))
    (fun i => coarseIndexedCandidateAllocation q L hB hq hL x y i (draws i)) indices
    (fun i _ => coarseIndexedCandidateAllocation_le_work q L hB hq hL x y i (draws i))
  have hm := coarseMinimumAllocation_le_work roots.1
  have hc := naturalCeilingAllocation_le_work (coarseMinimumWithWork roots.1).1
  unfold coarseIndexedInitialAllocation coarseIndexedInitialWithWork
  dsimp only
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · change arithmeticMapAllocation
        (fun i => coarseIndexedCandidateAllocation q L hB hq hL x y i (draws i)) indices +
        indices.length + coarseMinimumAllocation roots.1 +
        naturalCeilingAllocation (coarseMinimumWithWork roots.1).1 + Nat.size N ≤
      2 * ((binaryNaturalCompareWithWork (2 * x.length) y.length).2 +
        (naturalListEqualWithWork x y).2 + roots.2 + (coarseMinimumWithWork roots.1).2 +
        (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).2 +
        (wordMinWithWork N.bits (naturalCeilingWithWork (coarseMinimumWithWork roots.1).1).1).2 + Nat.size N + 6)
    change arithmeticMapAllocation
      (fun i => coarseIndexedCandidateAllocation q L hB hq hL x y i (draws i)) indices +
      indices.length ≤ 2 * roots.2 at hr
    omega

open Filter in
/-- Every draw has polynomial scratch, including outcomes outside the success event. -/
theorem computedCoarseIndexedInitialAllocation_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (hB : 0 < B) (hq : 0 < inputHeight N ^ 4) (hL : 0 < 64 * inputHeight N)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      coarseIndexedInitialAllocation (inputHeight N ^ 4) (64 * inputHeight N) N
        hB hq hL x y draws ≤ (N + 2) ^ 181 := by
  filter_upwards [computedCoarseIndexedInitialWithWork_polynomial] with N hN
  intro B d x y hBdef hddef hsize hsymbols hB hq hL draws
  have hw := hN B d x y hBdef hddef hsize hsymbols hB hq hL draws
  have ha := coarseIndexedInitialAllocation_le_work (inputHeight N ^ 4) (64 * inputHeight N) N hB hq hL x y draws
  calc
    _ ≤ 2 * (N + 2) ^ 180 := ha.trans (Nat.mul_le_mul_left 2 hw)
    _ ≤ (N + 2) * (N + 2) ^ 180 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := (pow_succ' (N + 2) 180).symm

end BinaryFraction
end EditApproximation

end OAI
