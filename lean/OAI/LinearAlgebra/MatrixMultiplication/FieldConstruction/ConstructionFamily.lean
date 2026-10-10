import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ConstructionData
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.Selection
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.RateLimit

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldConstructionFamily

open MatrixMultiplication.Foundation AllFieldHistory AllFieldConstructionData
open AllFieldConstructionRates Filter
open scoped BigOperators Topology Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ}

theorem exists_width_eventually_data (allocation : Allocation)
    {slack widthMax : ℝ} (hslack : 0 < slack) (hmax : 0 < widthMax) :
    ∃ width : ℝ, 0 < width ∧ width ≤ widthMax ∧
      ∀ᶠ m : ℕ in atTop, Nonempty (Data (K := K) allocation m width slack) := by
  let Index := Fin (K + 2) × Placement
  have hindex : (Finset.univ : Finset Index).Nonempty :=
    ⟨(⟨0, by omega⟩, Equiv.refl _), Finset.mem_univ _⟩
  have hb (i : Index) :=
    AllFieldGroupSelection.exists_threshold_eventually_selected
      (K := K) (tick := i.1.val) allocation i.2 hslack hmax
  choose threshold hpositive hmaximum hselected using hb
  let width := Finset.univ.inf' hindex threshold
  have hwidth : 0 < width := by
    apply (Finset.lt_inf'_iff hindex).mpr
    intro i _
    exact hpositive i
  have hbound (i : Index) : width ≤ threshold i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  have hwidthMax : width ≤ widthMax :=
    (hbound hindex.choose).trans (hmaximum hindex.choose)
  have hgroups : ∀ᶠ m : ℕ in atTop, ∀ i : Index,
      Nonempty (AllFieldGroupSelection.Selected (K := K) (tick := i.1.val)
        allocation m width i.2 slack) :=
    Filter.eventually_all.mpr (fun i => hselected i width hwidth (hbound i))
  have hthresholds : ∀ᶠ m : ℕ in atTop, ∀ t : Fin (K + 2),
      AllFieldHistoryRecovery.minimumDilation (K := K) (tick := t.val) allocation width ≤ m :=
    Filter.eventually_all.mpr (fun _ => eventually_ge_atTop _)
  refine ⟨width, hwidth, hwidthMax, ?_⟩
  filter_upwards [AllFieldInitialChoice.eventually_nonempty (K := K) allocation hslack,
    hgroups, hthresholds] with m hinitial hgroup hthreshold
  exact ⟨{ initial := Classical.choice hinitial
           groups := fun t sigma => Classical.choice (hgroup (t, sigma))
           threshold := hthreshold }⟩

def yieldRate (allocation : Allocation) (slack : ℝ) : ℝ :=
  AllFieldInitialEntropy.nativeH0 + AllFieldScheduledYield.physicalYield K allocation / K -
    (1 + 6 * (K + 2) : ℕ) * slack /
      ((K : ℝ) * denominator (K := K) allocation)

theorem exists_family (F : Type*) [Field F] (hK : 0 < K)
    (allocation : Allocation) {slack : ℝ} (hslack : 0 < slack)
    (hslots : ∀ slot : Slot K, slack ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot) :
    ∃ (W : ℕ → AllFieldWitness F) (scale : ℕ → ℝ),
      AllFieldRateLimit.HasRates W scale (yieldRate (K := K) allocation slack)
        AllFieldTerminalRates.S (8 * Real.log 7) := by
  obtain ⟨width, hwidth, _hmax, hd⟩ := exists_width_eventually_data
    (K := K) allocation hslack (show (0 : ℝ) < 1 by norm_num)
  have hterminal := (terminalDilation_tendsto K).eventually hd
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (hterminal.and (eventually_gt_atTop (0 : ℕ)))
  let data (n : ℕ) : Data (K := K) allocation
      (AllFieldTerminalRates.terminalDilation K (n + M)) width slack :=
    Classical.choice (hM (n + M) (Nat.le_add_left M n)).1
  have hn (n : ℕ) : 0 < n + M := (hM (n + M) (Nat.le_add_left M n)).2
  let W (n : ℕ) := witness (F := F) allocation width slack (n + M)
    (hn n) hwidth hslots (data n)
  let scale (n : ℕ) : ℝ := (K : ℝ) *
    AllFieldTerminalRates.terminalLength allocation K (n + M)
  refine ⟨W, scale, ?_⟩
  refine { scale_positive := ?_, yield_limit := ?_, volume_limit := ?_, rank_limit := ?_ }
  · apply Eventually.of_forall
    intro n
    exact mul_pos (Nat.cast_pos.mpr hK)
      (Nat.cast_pos.mpr (AllFieldTerminalRates.terminalLength_pos allocation (hn n)))
  · have h := (selected_terminal_rate hK allocation slack hslots).comp
      (tendsto_add_atTop_nat M)
    apply h.congr
    intro n
    simp only [Function.comp_def, W, scale, witness_multiplicity]
  · have h := (AllFieldTerminalRates.tendsto_terminalVolume hK allocation).comp
      (tendsto_add_atTop_nat M)
    apply h.congr
    intro n
    simp only [Function.comp_def, W, scale, witness_volume]
  · have h := (source_rank_terminal_rate hK allocation width).comp
      (tendsto_add_atTop_nat M)
    apply h.congr
    intro n
    simp only [Function.comp_def, W, scale, witness_rankBound]

theorem fixed_prescription_constraint (F : Type*) [Field F] (hK : 0 < K)
    (allocation : Allocation) {slack : ℝ} (hslack : 0 < slack)
    (hslots : ∀ slot : Slot K, slack ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot) :
    yieldRate (K := K) allocation slack + (Arithmetic.omega F / 3) *
      AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
  obtain ⟨W, scale, h⟩ := exists_family F hK allocation hslack hslots
  exact AllFieldRateLimit.inequality_of_rates h

theorem fixed_allocation_constraint (F : Type*) [Field F] (hK : 0 < K)
    (allocation : Allocation) (hcapacity : ∀ slot : Slot K, 0 < capacity allocation slot) :
    AllFieldInitialEntropy.nativeH0 + AllFieldScheduledYield.physicalYield K allocation / K +
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨slack, hslack, hslots, hloss⟩ :=
    exists_slack_for_loss hK allocation hcapacity hη
  have h := fixed_prescription_constraint F hK allocation hslack hslots
  unfold yieldRate at h
  linarith

end MatrixMultiplication.AllFieldConstructionFamily

end

end OAI
