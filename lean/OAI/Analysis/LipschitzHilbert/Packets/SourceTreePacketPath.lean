import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeExitBound

namespace OAI

/-! The finite tree conservation law uses precisely the original packet
active path. The node envelope controls its terminal cost, so deleting
the small bad-top mass yields domination by the good physical paths. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]
variable (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
  (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ)
  (assigned : σ → τ) (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
  (phase : ℕ → ℂ) (a α p : ℝ) {Kb : ℕ} (shift : Fin Kb) (x : X)

theorem sourceTree_packet_path_mass (top : τ) :
    g.sourceTreePathMass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift) x top =
      g.shiftedPathMass tops slope precision cutoff weight shift top x := rfl

theorem sourceTree_packet_path_ratio (top : τ) (j : ℕ) :
    g.sourceTreePathRatio tops slope precision cutoff weight (ShiftedBlocks.endpoint shift)
      (fun j cell => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
        packets assigned stop (value x) phase a x (ShiftedBlocks.endpoint shift j) cell)
      α p x top j =
    g.sourceShiftedPathRatio tops slope precision cutoff weight K gap
      packets assigned stop value phase a α p shift top x j := rfl

theorem sourceTree_packet_active_path (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 ≤ weight t x) (hKb : 0 < Kb) (top : τ) (htop : top ∈ tops)
    (count : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift count)) :
    (∏ j ∈ Finset.range (firstMassStop
      (g.sourceTreePathMass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift) x top)
      count M),
      g.sourceTreePathRatio tops slope precision cutoff weight (ShiftedBlocks.endpoint shift)
        (fun j cell => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
          packets assigned stop (value x) phase a x (ShiftedBlocks.endpoint shift j) cell)
        α p x top j) =
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a α p M shift top count x := by
  rw [g.source_active_path_eq_stopped_product tops slope precision cutoff weight hp hw
    K gap packets assigned stop value phase a α p M hM hKb shift top htop count hterminal x]
  rfl

theorem sourceTree_packet_good_path_domination
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x) (hKb : 0 < Kb)
    (count : ℕ) (cell : ℤ) (M C : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C)
    (hα : 1 ≤ α) (hp0 : 0 ≤ p)
    (hne : (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).Nonempty)
    (hroot : M < g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell x)
    (hterminal : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift count))
    (henvelope : ∀ j ≤ count, ∀ cell,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift j) cell‖ ≤
        C*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift j) cell x)
    (bad : Finset τ)
    (hbadS : bad ⊆ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell)
    (hbad : (1+C^p*(M+1)^(α-1))*(∑ t ∈ bad, weight t x) ≤ 1/2) :
    vertexAmount (g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell x)
      (g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell) α p ≤
      2*(1+C^p*(M+1)^(α-1))*
        ∑ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell\bad,
          weight t x*g.sourceActivePathValue tops slope precision cutoff weight K gap packets
            assigned stop value phase a α p M shift t count x := by
  let A := fun j cell => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
    packets assigned stop (value x) phase a x (ShiftedBlocks.endpoint shift j) cell
  have hexit (t : τ)
      (ht : t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell) :
      g.sourceTreeExit tops slope precision cutoff weight (ShiftedBlocks.endpoint shift) A α p x
        (firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight
          (ShiftedBlocks.endpoint shift) x t) count M) t ≤ 1+C^p*(M+1)^(α-1) := by
    have htt := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
    exact g.sourceTree_stop_exit_bound tops slope precision cutoff weight hw
      (ShiftedBlocks.endpoint shift) A α p M C hα hp0 (zero_le_one.trans hM) hC x count
      t htt.1 (hterminal t ht) (fun j hj _ => henvelope j hj _)
  have h := g.sourceTree_good_path_domination tops slope precision cutoff weight hp hw
    (ShiftedBlocks.endpoint shift) (ShiftedBlocks.endpoint_strictMono hKb shift).monotone
    A α p M (1+C^p*(M+1)^(α-1)) hM x count cell hne hroot hterminal hexit bad hbadS hbad
  change vertexAmount _ _ _ _ ≤ _ at h
  apply h.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have htt := (g.mem_cellTops _ _ _ _ _ _ _).mp (Finset.mem_sdiff.mp ht).1
  rw [g.sourceTree_packet_active_path tops slope precision cutoff weight K gap packets assigned
    stop value phase a α p shift x hp (fun t x => (hw t x).le) hKb t htt.1 count M
    (zero_le_one.trans hM) (hterminal t (Finset.mem_sdiff.mp ht).1)]

/-- A single pointwise majorant treats both small and active root masses.
Its two terms are the ordinary top mass and the already integrated good
physical paths, with the same terminal-envelope constant. -/
theorem sourceTree_packet_vertex_bound
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x) (hKb : 0 < Kb)
    (count : ℕ) (cell : ℤ) (M C : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C)
    (hα : 1 ≤ α) (hp0 : 0 ≤ p)
    (hne : (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell).Nonempty)
    (hterminal : ∀ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell,
      ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift count))
    (henvelope : ∀ j ≤ count, ∀ cell,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift j) cell‖ ≤
        C*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift j) cell x)
    (bad : Finset τ)
    (hbadS : bad ⊆ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell)
    (hbad : (1+C^p*(M+1)^(α-1))*(∑ t ∈ bad, weight t x) ≤ 1/2) :
    vertexAmount (g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell x)
      (g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell) α p ≤
      (1+C^p*(M+1)^(α-1))*
        g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift 0) cell x+
      2*(1+C^p*(M+1)^(α-1))*
        ∑ t ∈ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell\bad,
          weight t x*g.sourceActivePathValue tops slope precision cutoff weight K gap packets
            assigned stop value phase a α p M shift t count x := by
  have hmass : 0 < g.mass tops slope precision cutoff weight
      (ShiftedBlocks.endpoint shift 0) cell x := by
    obtain ⟨t,ht⟩ := hne
    exact g.mass_pos_of_member tops slope precision cutoff weight hw _ _ x ht
  have hcost : 0 ≤ 1+C^p*(M+1)^(α-1) := by positivity
  have hsum : 0 ≤ ∑ t ∈
      g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint shift 0) cell\bad,
      weight t x*g.sourceActivePathValue tops slope precision cutoff weight K gap packets
        assigned stop value phase a α p M shift t count x := by
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg (hw t x).le
      (g.sourceActivePathValue_nonneg tops slope precision cutoff weight
        (fun t x => (hw t x).le) K gap packets assigned stop value phase a α p M shift t count x)
  by_cases hroot : M < g.mass tops slope precision cutoff weight
      (ShiftedBlocks.endpoint shift 0) cell x
  · have h := g.sourceTree_packet_good_path_domination tops slope precision cutoff weight K gap
      packets assigned stop value phase a α p shift x hp hw hKb count cell M C hM hC hα hp0
      hne hroot hterminal henvelope bad hbadS hbad
    exact h.trans (le_add_of_nonneg_left (mul_nonneg hcost hmass.le))
  · have hb := source_exceptional_factor_le
      (g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (ShiftedBlocks.endpoint shift 0) cell)
      hmass le_rfl (show g.mass tops slope precision cutoff weight
        (ShiftedBlocks.endpoint shift 0) cell x ≤ M+1 by linarith [le_of_not_gt hroot])
      hC hα hp0 (henvelope 0 (Nat.zero_le _) cell)
    have hsmall := (div_le_iff₀ hmass).mp hb
    exact hsmall.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hsum))

end LipschitzHilbert.AngularGrid

end

end OAI
