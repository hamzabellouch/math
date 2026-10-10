import OAI.NumberTheory.Ostmann.Construction.SelectedCellTiers

namespace OAI

/-! # Constructing finite tiers from the prescribed selected cells -/
namespace Ostmann
open Filter
open scoped Classical

theorem eventual_selected_tier_budgets (k : ℕ) (hk : 0 < k)
    (a C BD Bz : ℝ) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ X J : ℝ, 0 < X → X ≤ Real.exp L →
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      48 * (64 * tailDefectBudget a C X + 2) ≤ J ∧
        (2 : ℝ) ^ k * (movingCompensationGapRate k BD Bz * L) ≤ J / 4 := by
  let T := 48 * (64 * tailCellLinearRate a C + 2) +
    (2 : ℝ) ^ k * movingCompensationGapRate k BD Bz
  have hrate := movingCompensationGapRate_nonneg k hk BD Bz hBD hBz
  have hT : 0 ≤ T := by
    dsimp only [T]
    positivity [tailCellLinearRate_nonneg a C]
  filter_upwards [arithmetic_exponent_absorption 0 (1 / 100) 0 T 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hbudget hL
  intro X J hX hXL hJ
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one, one_mul] at hbudget
  have hTL : T * L ≤ Real.exp ((1 / 100 : ℝ) * L) := by
    have hnonneg : 0 ≤ T * L := mul_nonneg hT (by linarith)
    linarith
  have hd := tailDefectBudget_linear a C L X hL hX hXL
  have hpow : 0 ≤ (2 : ℝ) ^ k * movingCompensationGapRate k BD Bz := by positivity
  have htail : 0 ≤ 48 * (64 * tailCellLinearRate a C + 2) := by
    positivity [tailCellLinearRate_nonneg a C]
  have hfirst : 48 * (64 * tailCellLinearRate a C + 2) * L ≤ T * L := by
    dsimp only [T]
    nlinarith only [mul_nonneg hpow (show 0 ≤ L by linarith)]
  have hsecond : (2 : ℝ) ^ k * (movingCompensationGapRate k BD Bz * L) ≤ T * L := by
    dsimp only [T]
    nlinarith only [mul_nonneg htail (show 0 ≤ L by linarith)]
  constructor
  · have hh : 48 * (64 * tailDefectBudget a C X + 2) ≤ T * L := by
      nlinarith only [hd, hL, hfirst]
    linarith only [hh, hTL, hJ, Real.exp_nonneg ((1 / 100 : ℝ) * L)]
  · linarith only [hsecond, hTL, hJ, Real.exp_nonneg ((1 / 100 : ℝ) * L)]

theorem selected_cells_prime_tiers
    {A B : Set ℕ} {N hi top : ℕ} {a C L X J cb BD Bz : ℝ} {D : Finset ℕ}
    {cs : List ℕ} (k : ℕ) (hk : 0 < k) (hL : 0 ≤ L)
    (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hcb : 0 ≤ cb)
    (hJ : 16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J)
    (herror : 48 * (64 * tailDefectBudget a C X + 2) ≤ J)
    (hgap : (2 : ℝ) ^ k * (movingCompensationGapRate k BD Bz * L) ≤ J / 4)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j)
      cs (movingCompensationTargets J (movingCompensationGaps k BD Bz L))) :
    let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
      (Real.exp ((6 / 1000 : ℝ) * L)) \ D
    ∃ tier : ℕ → ℕ,
      (∀ n < cs.length, ∀ p ∈ completedCompensationSets A B N X hi D top cs n,
        tier p = n) ∧
      (∀ n m offset, offset ≤ cs.length →
        ∃ tierB : MovingRegularSlot n (scheduledSmallLength (cs.drop offset)) m → ℕ,
          (∀ i, offset ≤ tierB i) ∧
          (∀ i p, p ∈ scheduledRegularPrimeSets (selectedTailCellPrimes A B N X hi D)
            Qb top (cs.drop offset) n m i → tier p = tierB i)) := by
  intro Qb
  let ds := movingCompensationGaps k BD Bz L
  let ws := movingCompensationTargets J ds
  let E := movingCompensationGapRate k BD Bz * L
  have hJ0 : 0 ≤ J := (by positivity : 0 ≤ 16 * Real.exp ((1 / 100 : ℝ) * L)).trans hJ
  have hE0 : 0 ≤ E := mul_nonneg (movingCompensationGapRate_nonneg k hk BD Bz hBD hBz) hL
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hEJ : E ≤ J / 4 := by
    have h := mul_le_mul_of_nonneg_right hp hE0
    simpa only [one_mul] using h.trans hgap
  have hd : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ E :=
    movingCompensationGaps_bounds k hk BD Bz L hBD hBz hL
  have hw := movingCompensationTargets_separated J E ds hJ0 hEJ hd
  have hlow (w : ℝ) (hw : w ∈ ws) : 3 * J / 4 ≤ w := by
    have h := (movingCompensationTargets_mem_bounds J E ds hJ0 hE0 hd w hw).1
    simp only [ds, movingCompensationGaps_length] at h
    linarith only [h, hgap]
  have hpair := selected_centers_pairwise_separated hcs hw (by linarith only [herror, hJ0])
  let R := selectedTailCellPrimes A B N X hi D top ∪ Qb
  have hR (i : Fin cs.length) :
      Disjoint R (selectedTailCellPrimes A B N X hi D (cs.get i)) := by
    have hi' : i.val < ws.length := by rw [← hcs.length_eq]; exact i.isLt
    have hc := hcs.get i.isLt hi'
    have hwi : ws.get ⟨i, hi'⟩ ∈ ws := List.get_mem _ _
    have hj := selected_top_compensation_gap htop hc hcb (hlow _ hwi) herror
    have htopdis := (selectedTailCellPrimes_disjoint_of_gap A B N hi X D _ _ hj).symm
    apply Finset.disjoint_left.mpr
    intro p hp hpi
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.disjoint_left.mp htopdis) hp hpi
    · have hb := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
      have hiLog := mem_primeLogCellSet_iff.mp
        (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hpi).1).1
      have hsmall : Real.exp ((6 / 1000 : ℝ) * L) ≤ (cs.get i : ℝ) := by
        have he : Real.exp ((6 / 1000 : ℝ) * L) ≤ Real.exp ((1 / 100 : ℝ) * L) :=
          Real.exp_le_exp.mpr (by nlinarith only [hL])
        have hwlo := hlow _ hwi
        have hci := hc.1
        linarith only [he, hwlo, hci, hJ, Real.exp_nonneg ((1 / 100 : ℝ) * L)]
      linarith only [hb.2.2.2, hiLog.2.2.1, hsmall]
  obtain ⟨tier, htier, hrest⟩ := exists_selected_prime_tiers A B N hi X D R cs hpair hR
  refine ⟨tier, ?_, ?_⟩
  · intro n hn p hp
    have he := completedCompensationCell_used top cs n hn
    unfold completedCompensationSets at hp
    rw [he, list_headD_drop_get cs 0 n hn] at hp
    exact htier ⟨n, hn⟩ p hp
  · intro n m offset hoffset
    exact exists_scheduled_prime_tiers A B N hi X D Qb top cs tier htier
      (fun p hp => hrest p (Finset.mem_union_left _ hp))
      (fun p hp => hrest p (Finset.mem_union_right _ hp)) n m offset hoffset

end Ostmann

end OAI
