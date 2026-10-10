import OAI.Combinatorics.EditApproximation.Coarse.CoarseArrayStorage

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Sum the stored bits of the four array results at each child step,
including every recursive child's array history. This allows all these
arrays to remain allocated instead of assuming prompt reclamation. -/
def coarseChildrenArrayHistory {B d : ℕ} {α : Type*} (k q L : ℕ) (two : BinaryFraction)
    (evaluate : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ)
    (history : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ → ℕ)
    (allowance : BinaryFraction) :
    List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d) → ℕ → ℕ
  | [], _ => 0
  | (child, draw, below) :: rest, start =>
    let threshold := (coarseChildThresholdWithWork B q allowance draw).1
    let childAllowance := (coarseChildAllowanceWithWork L threshold).1
    let evaluated := (evaluate child below childAllowance start).1
    let penalty := (coarseBinaryPenaltyWithWork two evaluated).1
    let scale := (coarseChildAllowanceWithWork q allowance).1
    let contribution := (coarseBinaryMapWithWork (coarseContributionWithWork threshold scale) penalty).1
    let remainder := coarseBinaryChildren k q L two evaluate allowance rest (start + child.word.length)
    let total := (coarseBinaryAddWithWork contribution remainder.1).1
    history child below childAllowance start +
      coarseChildrenArrayHistory k q L two evaluate history allowance rest (start + child.word.length) +
      coarseArrayStorage evaluated + coarseArrayStorage penalty +
      coarseArrayStorage contribution + coarseArrayStorage total

def coarseBinaryArrayHistory {B : ℕ} {α : Type*} [DecidableEq α]
    (k q L : ℕ) (frame : List (Option α)) (two : BinaryFraction) :
    {d : ℕ} → CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ → ℕ
  | _, tree, draws, allowance, start =>
    if (leWithWork (nat tree.word.length) allowance).1 then 1 else
    match tree, draws with
    | .leaf letter, leafDraw =>
      coarseArrayStorage (coarseBinaryEval k q L frame two (.leaf letter) leafDraw allowance start).1
    | .branch children, (draws, below) =>
      coarseArrayStorage (coarseBinaryEval k q L frame two (.branch children) (draws, below) allowance start).1 +
        coarseChildrenArrayHistory k q L two
          (fun child => coarseBinaryEval k q L frame two child)
          (fun child => coarseBinaryArrayHistory k q L frame two child)
          allowance (List.ofFn fun i => (children i, draws i, below i)) start

theorem coarseChildrenArrayHistory_bound {B d : ℕ} {α : Type*}
    (k q L N V D A C : ℕ) (two allowance : BinaryFraction)
    (evaluate : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ)
    (history : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ → ℕ)
    (weight : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (hB : 0 < B) (hlen : children.length ≤ B) (htwo : two.value = 2) (htw : two.width ≤ A)
    (ha : allowance.width ≤ A) (hBbits : Nat.size B + 2 ≤ A)
    (hqbits : Nat.size q + 2 ≤ A) (hLbits : Nat.size L + 2 ≤ A) (hNbits : Nat.size N ≤ A)
    (ht : ∀ draw : Fin B, (coarseChildThresholdWithWork B q allowance draw).1.width ≤ A)
    (hs : CoarseGridCell two (coarseChildAllowanceWithWork q allowance).1 k D A)
    (hbound : Nat.size (B * (V + k) + 2) + 2 * D + 1 ≤ A)
    (he : ∀ child draw below, (child, draw, below) ∈ children → ∀ s,
      s + child.word.length ≤ N →
      CoarseBinaryBox two (2 * k + 1) V D A
        (evaluate child below (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance draw).1).1 s).1 ∧
      (evaluate child below (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance draw).1).1 s).2 ≤
        (100000000 * (A + 1) ^ 2) * weight child below
          (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance draw).1).1)
    (hh : ∀ child draw below, (child, draw, below) ∈ children → ∀ s,
      s + child.word.length ≤ N →
      history child below (coarseChildAllowanceWithWork L
        (coarseChildThresholdWithWork B q allowance draw).1).1 s ≤
      C * weight child below (coarseChildAllowanceWithWork L
        (coarseChildThresholdWithWork B q allowance draw).1).1)
    (start : ℕ) (hstart : start + coarseChildrenSpan children ≤ N) :
    coarseChildrenArrayHistory k q L two evaluate history allowance children start ≤
      C * coarseBinaryChildrenWeight q L weight allowance children +
        4 * (1 + (2 * k + 1) * (2 * A + 3)) * children.length := by
  have hvbound : Nat.size (V + 2) + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size
      (by nlinarith : V + 2 ≤ B * (V + k) + 2)) _) _).trans hbound
  have hmapped : Nat.size (V + k) + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size
      (by nlinarith : V + k ≤ B * (V + k) + 2)) _) _).trans hbound
  induction children generalizing start with
  | nil => simp only [coarseChildrenArrayHistory, coarseBinaryChildrenWeight, List.length_nil,
      Nat.mul_zero, Nat.add_zero, le_refl]
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    have hspan : start + (child.word.length + coarseChildrenSpan rest) ≤ N := hstart
    have hc := he child draw below List.mem_cons_self start (by omega)
    have hhistory := hh child draw below List.mem_cons_self start (by omega)
    have hrest := ih (by simp only [List.length_cons] at hlen; omega)
      (fun child draw below hmem => he child draw below (List.mem_cons_of_mem _ hmem))
      (fun child draw below hmem => hh child draw below (List.mem_cons_of_mem _ hmem))
      (start + child.word.length) (by omega)
    have hr := coarseBinaryChildren_bounds k q L N V D A two allowance evaluate weight rest
      hB (by simp only [List.length_cons] at hlen; omega) htwo htw ha hBbits hqbits hLbits hNbits ht hs hbound
      (fun child draw below hmem => he child draw below (List.mem_cons_of_mem _ hmem))
      (start + child.word.length) (by omega)
    let threshold := (coarseChildThresholdWithWork B q allowance draw).1
    let childAllowance := (coarseChildAllowanceWithWork L threshold).1
    let evaluated := (evaluate child below childAllowance start).1
    let penalty := (coarseBinaryPenaltyWithWork two evaluated).1
    let scale := (coarseChildAllowanceWithWork q allowance).1
    let contribution := (coarseBinaryMapWithWork (coarseContributionWithWork threshold scale) penalty).1
    let remainder := (coarseBinaryChildren k q L two evaluate allowance rest (start + child.word.length)).1
    have hpen : CoarseBinaryBox two (2 * k + 1) V D A penalty :=
      coarseBinaryPenaltyWithWork_box two _ V D A evaluated hc.1 htwo htw hvbound
    have hcon : CoarseBinaryBox two (2 * k + 1) (V + k) D A contribution :=
      coarseBinaryMapWithWork_box two _ V (V + k) D A _ penalty hpen
        (fun a ha => coarseContributionWithWork_bounds two threshold scale a V k D A ha hs hmapped)
    have habound : Nat.size ((V + k) + rest.length * (V + k)) + 2 * D + 1 ≤ A := by
      apply le_trans _ hbound
      apply Nat.add_le_add_right
      apply Nat.add_le_add_right
      apply Nat.size_le_size
      simp only [List.length_cons] at hlen
      nlinarith
    have htotal := coarseBinaryAddWithWork_box two (2 * k + 1) (V + k)
      (rest.length * (V + k)) D A contribution remainder hcon hr.1 habound
    have hevalBits := coarseArrayStorage_le two _ _ D A evaluated hc.1
    have hpenBits := coarseArrayStorage_le two _ _ D A penalty hpen
    have hconBits := coarseArrayStorage_le two _ _ D A contribution hcon
    have htotalBits := coarseArrayStorage_le two _ _ D A _ htotal
    let F := 1 + (2 * k + 1) * (2 * A + 3)
    change history child below childAllowance start ≤ C * weight child below childAllowance at hhistory
    change coarseChildrenArrayHistory k q L two evaluate history allowance rest (start + child.word.length) ≤
      C * coarseBinaryChildrenWeight q L weight allowance rest + 4 * F * rest.length at hrest
    have hfour : coarseArrayStorage evaluated + coarseArrayStorage penalty +
        coarseArrayStorage contribution +
        coarseArrayStorage (coarseBinaryAddWithWork contribution remainder).1 ≤ 4 * F := by
      dsimp only [F]
      omega
    calc
      _ ≤ C * weight child below childAllowance +
          (C * coarseBinaryChildrenWeight q L weight allowance rest + 4 * F * rest.length) +
          4 * F := by
        change history child below childAllowance start +
          coarseChildrenArrayHistory k q L two evaluate history allowance rest (start + child.word.length) +
          coarseArrayStorage evaluated + coarseArrayStorage penalty + coarseArrayStorage contribution +
          coarseArrayStorage (coarseBinaryAddWithWork contribution remainder).1 ≤ _
        omega
      _ = _ := by
        simp only [coarseBinaryChildrenWeight, List.length_cons]
        dsimp only [F, childAllowance, threshold]
        ring

end BinaryFraction
end EditApproximation

end OAI
