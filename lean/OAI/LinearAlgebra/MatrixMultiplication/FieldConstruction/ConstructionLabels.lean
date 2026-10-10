import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ScheduledYield
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ScheduledPositivity
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.TerminalRates
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.FloorExponentialRates

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldConstructionRates

open MatrixMultiplication.Foundation AllFieldHistory AllFieldScheduledYield
open AllFieldActiveLaws Filter
open scoped BigOperators Topology Classical

variable {K : ℕ}

def denominator (allocation : Allocation) : ℕ := populationLength (K := K) allocation 1

theorem denominator_pos (allocation : Allocation) : 0 < denominator (K := K) allocation :=
  AllFieldPopulationCounts.blockLength_pos _ (by decide)

theorem population_length (allocation : Allocation) (m : ℕ) :
    populationLength (K := K) allocation m = m * denominator (K := K) allocation :=
  populationLength_dilation allocation m

theorem populationLength_tendsto (allocation : Allocation) :
    Tendsto (populationLength (K := K) allocation) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with m hm
  rw [population_length]
  exact hm.trans (by simpa using Nat.mul_le_mul_left m (denominator_pos allocation))

abbrev Slot (K : ℕ) := Unit ⊕ (Fin (K + 2) × Placement)

def capacity (allocation : Allocation) : Slot K → ℝ
  | .inl _ => (K : ℝ) * AllFieldInitialEntropy.nativeH0
  | .inr p => Staggering.minCapacity
      (physicalTickCapacity allocation p.1.val (workCapacity (K := K)) p.2)

def selectionRate (allocation : Allocation) (δ : ℝ) (slot : Slot K) : ℝ :=
  (denominator (K := K) allocation : ℝ) * capacity allocation slot - δ

def initialCount (allocation : Allocation) (δ : ℝ) (m : ℕ) : ℕ :=
  FloorExponentialRates.count (selectionRate (K := K) allocation δ (.inl ())) m

def groupCount (allocation : Allocation) (δ : ℝ) (m : ℕ)
    (tick : Fin (K + 2)) (σ : Placement) : ℕ :=
  FloorExponentialRates.count (selectionRate allocation δ (.inr (tick, σ))) m

theorem initialCount_eq (allocation : Allocation) (δ : ℝ) (m : ℕ) :
    initialCount (K := K) allocation δ m =
      ⌊Real.exp ((m : ℝ) * ((populationLength (K := K) allocation 1 : ℝ) *
        ((K : ℝ) * AllFieldInitialEntropy.nativeH0) - δ))⌋₊ := rfl

theorem groupCount_eq_native (allocation : Allocation) (δ : ℝ) (m : ℕ)
    (tick : Fin (K + 2)) (σ : Placement) :
    groupCount allocation δ m tick σ =
      ⌊Real.exp ((m : ℝ) * ((populationLength (K := K) allocation 1 : ℝ) *
        ((1 / 6 : ℝ) * Staggering.minCapacity (FiniteSchedule.tickCapacity K
          AllFieldNativeCapacity.nativeLA AllFieldNativeCapacity.nativeLB
          (AllFieldNativeCapacity.nativeLC (fun i => (allocation.mass i : ℝ))) tick.val)) - δ))⌋₊ := by
  unfold groupCount FloorExponentialRates.count selectionRate
  simp only [capacity, physical_order_native_capacity,
    PhysicalOrders.minCapacity_mul _ _ (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  rfl

abbrev SelectedLabels (allocation : Allocation) (δ : ℝ) (m : ℕ) :=
  Fin (initialCount (K := K) allocation δ m) ×
    ∀ tick : Fin (K + 2), ∀ σ : Placement, Fin (groupCount allocation δ m tick σ)

theorem card_selected (allocation : Allocation) (δ : ℝ) (m : ℕ) :
    Fintype.card (SelectedLabels (K := K) allocation δ m) =
      initialCount (K := K) allocation δ m *
        ∏ tick : Fin (K + 2), ∏ σ : Placement, groupCount allocation δ m tick σ := by
  simp only [SelectedLabels, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]

theorem card_selected_product (allocation : Allocation) (δ : ℝ) (m : ℕ) :
    Fintype.card (SelectedLabels (K := K) allocation δ m) =
      (∏ slot : Slot K, FloorExponentialRates.count (selectionRate allocation δ slot) m) := by
  rw [card_selected]
  simp [Slot, initialCount, groupCount, Fintype.prod_sum_type, Fintype.prod_prod_type]

theorem card_selected_from_factors
    (Initial : Type*) [Fintype Initial]
    (Groups : Fin (K + 2) → Placement → Type*) [∀ tick σ, Fintype (Groups tick σ)]
    (allocation : Allocation) (δ : ℝ) (m : ℕ)
    (hI : Fintype.card Initial = initialCount (K := K) allocation δ m)
    (hG : ∀ tick σ, Fintype.card (Groups tick σ) = groupCount allocation δ m tick σ) :
    Fintype.card (Initial × ∀ tick σ, Groups tick σ) =
      Fintype.card (SelectedLabels (K := K) allocation δ m) := by
  simp only [Fintype.card_prod, Fintype.card_pi, hI, hG, Fintype.card_fin]

theorem slot_card : Fintype.card (Slot K) = 1 + 6 * (K + 2) := by
  simp [Slot, Placement, Fintype.card_perm, Nat.factorial_succ]
  omega

theorem sum_capacity (allocation : Allocation) :
    (∑ slot : Slot K, capacity allocation slot) =
      (K : ℝ) * AllFieldInitialEntropy.nativeH0 + physicalYield K allocation := by
  simp only [Slot, Fintype.sum_sum_type, capacity, Fintype.sum_unique,
    Fintype.sum_prod_type]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun tick : ℕ =>
    ∑ σ : Placement, Staggering.minCapacity
      (physicalTickCapacity allocation tick (workCapacity (K := K)) σ)) (K + 2)

theorem sum_selectionRate (allocation : Allocation) (δ : ℝ) :
    (∑ slot : Slot K, selectionRate allocation δ slot) =
      (denominator (K := K) allocation : ℝ) *
        ((K : ℝ) * AllFieldInitialEntropy.nativeH0 + physicalYield K allocation) -
      (1 + 6 * (K + 2) : ℕ) * δ := by
  simp only [selectionRate, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, slot_card, sum_capacity]

theorem selected_pos (allocation : Allocation) (δ : ℝ)
    (hδ : ∀ slot : Slot K, δ ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot) (m : ℕ) :
    0 < Fintype.card (SelectedLabels (K := K) allocation δ m) := by
  rw [card_selected_product]
  exact Finset.prod_pos fun slot _ =>
    FloorExponentialRates.count_pos (sub_nonneg.mpr (hδ slot)) m

theorem selected_rate (hK : 0 < K) (allocation : Allocation) (δ : ℝ)
    (hδ : ∀ slot : Slot K, δ ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card
      (SelectedLabels (K := K) allocation δ m) : ℝ) /
      ((K : ℝ) * populationLength (K := K) allocation m)) atTop
      (𝓝 (AllFieldInitialEntropy.nativeH0 + physicalYield K allocation / K -
        (1 + 6 * (K + 2) : ℕ) * δ /
          ((K : ℝ) * denominator (K := K) allocation))) := by
  have h := (FloorExponentialRates.tendsto_log_prod_count_div_nat
    (selectionRate (K := K) allocation δ) (fun slot => sub_nonneg.mpr (hδ slot))).div_const
    ((K : ℝ) * denominator (K := K) allocation)
  rw [sum_selectionRate] at h
  have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  have hd : (denominator (K := K) allocation : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (denominator_pos allocation).ne'
  have hr : ((denominator (K := K) allocation : ℝ) *
      ((K : ℝ) * AllFieldInitialEntropy.nativeH0 + physicalYield K allocation) -
      (1 + 6 * (K + 2) : ℕ) * δ) / ((K : ℝ) * denominator (K := K) allocation) =
      AllFieldInitialEntropy.nativeH0 + physicalYield K allocation / K -
        (1 + 6 * (K + 2) : ℕ) * δ /
          ((K : ℝ) * denominator (K := K) allocation) := by
    field_simp [hk, hd]
  rw [hr] at h
  apply h.congr
  intro m
  rw [card_selected_product, population_length, Nat.cast_mul]
  ring

theorem exists_positive_slack (allocation : Allocation)
    (hcap : ∀ slot : Slot K, 0 < capacity allocation slot) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, δ ≤ η → ∀ slot : Slot K,
      δ ≤ (denominator (K := K) allocation : ℝ) * capacity allocation slot := by
  let η := Finset.univ.inf' (show (Finset.univ : Finset (Slot K)).Nonempty from
    ⟨.inl (), Finset.mem_univ _⟩)
    (fun slot => (denominator (K := K) allocation : ℝ) * capacity allocation slot)
  refine ⟨η, ?_, ?_⟩
  · apply (Finset.lt_inf'_iff _).mpr
    intro slot _
    exact mul_pos (Nat.cast_pos.mpr (denominator_pos allocation)) (hcap slot)
  · intro δ hδ slot
    exact hδ.trans (Finset.inf'_le _ (Finset.mem_univ slot))

theorem exists_slack_for_loss (hK : 0 < K) (allocation : Allocation)
    (hcap : ∀ slot : Slot K, 0 < capacity allocation slot)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ slot : Slot K, δ ≤ (denominator (K := K) allocation : ℝ) *
        capacity allocation slot) ∧
      (1 + 6 * (K + 2) : ℕ) * δ /
        ((K : ℝ) * denominator (K := K) allocation) < η := by
  obtain ⟨bound, hbound, hslots⟩ := exists_positive_slack allocation hcap
  have hk : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hd : (0 : ℝ) < denominator (K := K) allocation :=
    Nat.cast_pos.mpr (denominator_pos allocation)
  have hc : (0 : ℝ) < (1 + 6 * (K + 2) : ℕ) := by positivity
  let target := η * ((K : ℝ) * denominator (K := K) allocation) /
    (1 + 6 * (K + 2) : ℕ)
  have ht : 0 < target := div_pos (mul_pos hη (mul_pos hk hd)) hc
  let δ := min bound target / 2
  have hm : 0 < min bound target := lt_min hbound ht
  have hδ : 0 < δ := div_pos hm (by norm_num)
  have hδmin : δ < min bound target := by dsimp [δ]; linarith
  refine ⟨δ, hδ, hslots δ (hδmin.le.trans (min_le_left _ _)), ?_⟩
  apply (div_lt_iff₀ (mul_pos hk hd)).mpr
  have hsmall := (lt_div_iff₀ hc).mp (hδmin.trans_le (min_le_right bound target))
  change δ * ((1 + 6 * (K + 2) : ℕ) : ℝ) <
    η * ((K : ℝ) * denominator (K := K) allocation) at hsmall
  simpa only [mul_comm δ] using hsmall

theorem capacity_pos_of_native (hK : 2 ≤ K) (allocation : Allocation)
    (ha : ∀ i, 0 < AllFieldNativeCapacity.nativeLA i)
    (hb : ∀ i, 0 < AllFieldNativeCapacity.nativeLB i)
    (hc : ∀ i, 0 < AllFieldNativeCapacity.nativeLC
      (fun j => (allocation.mass j : ℝ)) i) (slot : Slot K) :
    0 < capacity allocation slot := by
  cases slot with
  | inl u => exact AllFieldScheduledPositivity.initial_capacity_pos K (by omega)
  | inr p =>
    exact AllFieldScheduledPositivity.physical_order_capacity_pos K p.1.val hK
      p.1.isLt allocation p.2 ha hb hc

theorem eventually_capacity_pos (hK : 2 ≤ K) (allocation : ℕ → Allocation)
    (h : ∀ i, Tendsto (fun j => ((allocation j).mass i : ℝ)) atTop
      (𝓝 (AllFieldNativeCapacity.nativeLambda i)))
    (ha : ∀ i, 0 < AllFieldNativeCapacity.nativeLA i)
    (hb : ∀ i, 0 < AllFieldNativeCapacity.nativeLB i)
    (hc : ∀ i, 0 < AllFieldNativeCapacity.nativeLC AllFieldNativeCapacity.nativeLambda i) :
    ∀ᶠ j in atTop, ∀ slot : Slot K, 0 < capacity (allocation j) slot := by
  filter_upwards [AllFieldScheduledPositivity.eventually_physical_order_capacity_pos
    K hK allocation h ha hb hc] with j hj
  intro slot
  cases slot with
  | inl u => exact AllFieldScheduledPositivity.initial_capacity_pos K (by omega)
  | inr p => exact hj p.1.val p.1.isLt p.2

theorem terminalDilation_mul_one (K m : ℕ) :
    AllFieldTerminalRates.terminalDilation K m =
      m * AllFieldTerminalRates.terminalDilation K 1 := by
  simp only [AllFieldTerminalRates.terminalDilation,
    AllFieldTerminalPopulations.dilation, one_mul]

theorem terminalDilation_tendsto (K : ℕ) :
    Tendsto (AllFieldTerminalRates.terminalDilation K) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with m hm
  rw [terminalDilation_mul_one]
  have hD := AllFieldTerminalRates.terminalDilation_pos (K := K) (m := 1) (by decide)
  have hmul : m ≤ m * AllFieldTerminalRates.terminalDilation K 1 := by
    simpa using Nat.mul_le_mul_left m hD
  exact hm.trans hmul

theorem terminal_denominator (allocation : Allocation) :
    AllFieldTerminalRates.terminalLength allocation K 1 =
      AllFieldTerminalRates.terminalDilation K 1 * denominator (K := K) allocation :=
  population_length allocation _

theorem selected_terminal_rate (hK : 0 < K) (allocation : Allocation) (δ : ℝ)
    (hδ : ∀ slot : Slot K, δ ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card
      (SelectedLabels (K := K) allocation δ (AllFieldTerminalRates.terminalDilation K m)) : ℝ) /
      ((K : ℝ) * AllFieldTerminalRates.terminalLength allocation K m)) atTop
      (𝓝 (AllFieldInitialEntropy.nativeH0 + physicalYield K allocation / K -
        (1 + 6 * (K + 2) : ℕ) * δ /
          ((K : ℝ) * denominator (K := K) allocation))) :=
  (selected_rate hK allocation δ hδ).comp (terminalDilation_tendsto K)

theorem selected_terminal_rate_of_cardinality
    (Labels : ℕ → Type*) [∀ m, Fintype (Labels m)]
    (hK : 0 < K) (allocation : Allocation) (δ : ℝ)
    (hδ : ∀ slot : Slot K, δ ≤ (denominator (K := K) allocation : ℝ) *
      capacity allocation slot)
    (cards : ∀ᶠ m : ℕ in atTop, Fintype.card (Labels m) = Fintype.card
      (SelectedLabels (K := K) allocation δ (AllFieldTerminalRates.terminalDilation K m))) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (Labels m) : ℝ) /
      ((K : ℝ) * AllFieldTerminalRates.terminalLength allocation K m)) atTop
      (𝓝 (AllFieldInitialEntropy.nativeH0 + physicalYield K allocation / K -
        (1 + 6 * (K + 2) : ℕ) * δ /
          ((K : ℝ) * denominator (K := K) allocation))) := by
  apply (selected_terminal_rate hK allocation δ hδ).congr'
  filter_upwards [cards] with m hm
  rw [hm]

end MatrixMultiplication.AllFieldConstructionRates

end

end OAI
