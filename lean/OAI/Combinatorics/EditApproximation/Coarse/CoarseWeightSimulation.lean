import OAI.Combinatorics.EditApproximation.Coarse.CoarseBinaryWeight

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseBinaryChildrenWeight_eq {B d : ℕ} {α : Type*} (q L : ℕ)
    (weight : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ)
    (arrays labels : CoarseSourceTree B α d → CoarseThresholdDraws B d → ℚ → ℕ)
    (allowance : BinaryFraction)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (he : ∀ child draw below, (child, draw, below) ∈ children →
      weight child below (coarseChildAllowanceWithWork L
        (coarseChildThresholdWithWork B q allowance draw).1).1 =
      arrays child below ((1 / L) * coarseChildThreshold B q allowance.value draw) +
      labels child below ((1 / L) * coarseChildThreshold B q allowance.value draw) + 1) :
    coarseBinaryChildrenWeight q L weight allowance children =
      coarseActiveChildrenWork q (1 / L) allowance.value arrays children +
      coarseLabelChildren q (1 / L) allowance.value labels children + children.length := by
  induction children with
  | nil => rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    rw [coarseBinaryChildrenWeight, he child draw below List.mem_cons_self,
      ih (fun child draw below hmem => he child draw below (List.mem_cons_of_mem _ hmem))]
    simp only [coarseActiveChildrenWork, coarseLabelChildren, List.length_cons]
    omega

 theorem coarseBinaryWeight_eq {B d : ℕ} {α : Type*}
    (k q L R : ℕ) (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (j : ℕ) (hdepth : j + d = R) (allowance : BinaryFraction)
    (ha : allowance.representation.den = coarseCommonDenominator 1 q L B R)
    (hpath : allowance.value.den ∣ (L * B * q) ^ j) :
    coarseBinaryWeight k q L tree draws allowance =
      coarseActiveArrayWork k q (1 / L) tree draws allowance.value +
      coarseLabelCount q (1 / L) tree draws allowance.value + 1 := by
  induction tree generalizing j allowance with
  | leaf letter =>
    have hp := leWithWork_value (nat (CoarseSourceTree.leaf (B := B) letter).word.length) allowance
    rw [nat_value] at hp
    rw [coarseBinaryWeight, coarseActiveArrayWork, coarseLabelCount]
    by_cases h : ((CoarseSourceTree.leaf (B := B) letter).word.length : ℚ) ≤ allowance.value
    · simp only [ite_eq_left (hp.mpr h), ite_eq_left h]
    · simp only [ite_eq_right (fun hh => h (hp.mp hh)), ite_eq_right h]
  | @branch d children ih =>
    obtain ⟨draws, below⟩ := draws
    have hp := leWithWork_value (nat (CoarseSourceTree.branch children).word.length) allowance
    rw [nat_value] at hp
    rw [coarseBinaryWeight, coarseActiveArrayWork, coarseLabelCount]
    by_cases h : ((CoarseSourceTree.branch children).word.length : ℚ) ≤ allowance.value
    · simp only [ite_eq_left (hp.mpr h), ite_eq_left h]
    · simp only [ite_eq_right (fun hh => h (hp.mp hh)), ite_eq_right h]
      have he : coarseBinaryChildrenWeight q L (fun child => coarseBinaryWeight k q L child)
          allowance (List.ofFn fun i => (children i, draws i, below i)) =
          coarseActiveChildrenWork q (1 / L) allowance.value
            (fun child => coarseActiveArrayWork k q (1 / L) child)
            (List.ofFn fun i => (children i, draws i, below i)) +
          coarseLabelChildren q (1 / L) allowance.value
            (fun child => coarseLabelCount q (1 / L) child)
            (List.ofFn fun i => (children i, draws i, below i)) + B := by
        refine (coarseBinaryChildrenWeight_eq q L (fun child => coarseBinaryWeight k q L child)
          (fun child => coarseActiveArrayWork k q (1 / L) child)
          (fun child => coarseLabelCount q (1 / L) child) allowance
          (List.ofFn fun i => (children i, draws i, below i)) ?_).trans ?_
        · intro child draw childBelow hmem
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          let threshold := (coarseChildThresholdWithWork B q allowance (draws i)).1
          let childAllowance := (coarseChildAllowanceWithWork L threshold).1
          have ht : threshold.value = coarseChildThreshold B q allowance.value (draws i) := by
            apply coarseChildThresholdWithWork_value
            rw [ha, ← hdepth]
            exact coarseThreshold_root_grid B q L j d allowance.value (draws i) hB hq hpath
          have htd : threshold.representation.den = coarseCommonDenominator 1 q L B R :=
            (coarseChildThresholdWithWork_den B q allowance (draws i)).trans ha
          have hcd : childAllowance.representation.den = coarseCommonDenominator 1 q L B R :=
            (coarseChildAllowanceWithWork_den L threshold).trans htd
          have hv : childAllowance.value = (1 / (L : ℚ)) *
              coarseChildThreshold B q allowance.value (draws i) := by
            have hg : (threshold.value / L).den ∣ threshold.representation.den := by
              rw [ht, htd, ← hdepth]
              rw [show coarseChildThreshold B q allowance.value (draws i) / (L : ℚ) =
                (1 / (L : ℚ)) * coarseChildThreshold B q allowance.value (draws i) by ring]
              exact coarseChildAllowance_root_grid B q L j d allowance.value (draws i) hB hq hL hpath
            have hz := coarseChildAllowanceWithWork_value L threshold hg
            change childAllowance.value = _ at hz
            rw [hz, ht]
            ring
          have hcp : childAllowance.value.den ∣ (L * B * q) ^ (j + 1) := by
            rw [hv]
            exact coarseChildAllowance_grid B q L j allowance.value (draws i) hB hq hL hpath
          have hc := ih i (below i) (j + 1) (by omega) childAllowance hcd hcp
          rw [hv] at hc
          exact hc
        · simp only [List.length_ofFn]
      rw [he]
      omega

 theorem coarseBinaryWeight_le {B d : ℕ} {α : Type*}
    (k q L R : ℕ) (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (j : ℕ) (hdepth : j + d = R) (allowance : BinaryFraction)
    (ha : allowance.representation.den = coarseCommonDenominator 1 q L B R)
    (hpath : allowance.value.den ∣ (L * B * q) ^ j) :
    coarseBinaryWeight k q L tree draws allowance ≤
      2 * coarseActiveArrayWork k q (1 / L) tree draws allowance.value + 1 := by
  rw [coarseBinaryWeight_eq k q L R tree draws hB hq hL j hdepth allowance ha hpath]
  have h := coarseLabelCount_le_arrayWork k (q : ℚ) (1 / L) tree draws allowance.value
  omega

end BinaryFraction
end EditApproximation

end OAI
