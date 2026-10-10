import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.NativeCapacity
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ActiveSums
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ActiveLaws
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialEntropy
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.StageCCapacity
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalContinuity
import Mathlib.Topology.Order.OrderClosed

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldScheduledYield

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldNativeCapacity
open Filter
open scoped BigOperators Topology

def workCapacity {K : ℕ} : Work K → Staggering.Capacity :=
  shapeCapacity stageACapacity stageBCapacity stageCCapacity

theorem workCapacity_stageC {K : ℕ} (h : PartC K) (i : Fin 3) :
    workCapacity (Work.stageC h) i = finiteEntropy
      (AllFieldStageCCapacity.stageCMarginal (cParameterParent h) (cShapeParent h)
        (cPriority h i)) := by
  rw [AllFieldStageCCapacity.stageCMarginal_priority_entropy]
  rfl

private theorem sum_interiorPairs (f : Shape × Shape → ℝ) :
    (interiorPairs.map f).sum =
      (positiveSecond.map fun t =>
        (((below t).filter positive).map fun u => f (t,u)).sum).sum := by
  unfold interiorPairs
  have h : ∀ xs : List Shape,
      ((xs.flatMap fun t => ((below t).filter positive).map fun u => (t,u)).map f).sum =
        (xs.map fun t => (((below t).filter positive).map fun u => f (t,u)).sum).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons t xs ih => simp [ih, List.map_map, Function.comp_def]
  exact h positiveSecond

theorem stageCSourceCapacity_native (allocation : Allocation) :
    stageCSourceCapacity allocation stageCCapacity =
      nativeLC (fun i => (allocation.mass i : ℝ)) := by
  funext i
  unfold stageCSourceCapacity stageCSourceSum nativeLC
  rw [sum_interiorPairs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  rw [show (∑ part : Fin 3, (allocation.mass part : ℝ) * stageCCapacity t u part i) =
      (1 - (allocation.mass i : ℝ)) * Real.log 2 +
        (allocation.mass i : ℝ) * binaryEntropyRate (binaryParameter t u) from
    AllFieldStageCCapacity.allocation_capacity allocation (binaryParameter t u) i]
  rfl

theorem active_native_capacity (K tick : ℕ) (allocation : Allocation) :
    activeAggregateCapacity allocation tick (workCapacity (K := K)) =
      FiniteSchedule.tickCapacity K nativeLA nativeLB
        (nativeLC (fun i => (allocation.mass i : ℝ))) tick := by
  rw [workCapacity, activeAggregateCapacity_shapeCapacity,
    stageCSourceCapacity_native]
  rfl

theorem physical_order_native_capacity (K tick : ℕ) (allocation : Allocation)
    (sigma : Placement) :
    physicalTickCapacity allocation tick (workCapacity (K := K)) sigma =
      fun i => (1 / 6 : ℝ) * FiniteSchedule.tickCapacity K nativeLA nativeLB
        (nativeLC (fun i => (allocation.mass i : ℝ))) tick i := by
  rw [physicalTickCapacity_eq_sixth, active_native_capacity]

theorem order_capacity_eq_physical (K tick : ℕ) (allocation : Allocation)
    (sigma : Placement) (i : Fin 3) :
    (∑ h : ActiveOrder K tick sigma,
      AllFieldActiveLaws.orderMass allocation h * workCapacity h.val.val.1 i) =
      physicalTickCapacity allocation tick (workCapacity (K := K)) sigma i := by
  rw [physicalTickCapacity_eq_sixth]
  rw [← (canonicalActiveEquivOrder K tick sigma).sum_comp
    (fun h : ActiveOrder K tick sigma =>
      AllFieldActiveLaws.orderMass allocation h * workCapacity h.val.val.1 i)]
  simp only [AllFieldActiveLaws.orderMass, canonicalActiveEquivOrder, amount,
    Rat.cast_div, Rat.cast_ofNat, activeAggregateCapacity,
    PhysicalOrders.aggregateCapacity, workAmount]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  change ((canonicalAmount allocation h.val.source : ℝ) / 6) *
    workCapacity h.val i = (1 / 6 : ℝ) *
      ((canonicalAmount allocation h.val.source : ℝ) * workCapacity h.val i)
  ring

theorem order_capacity_eq_native (K tick : ℕ) (allocation : Allocation)
    (sigma : Placement) (i : Fin 3) :
    (∑ h : ActiveOrder K tick sigma,
      AllFieldActiveLaws.orderMass allocation h * workCapacity h.val.val.1 i) =
      (1 / 6 : ℝ) * FiniteSchedule.tickCapacity K nativeLA nativeLB
        (nativeLC (fun j => (allocation.mass j : ℝ))) tick i := by
  rw [order_capacity_eq_physical, physical_order_native_capacity]

theorem order_dilation_capacity (K tick : ℕ) (allocation : Allocation)
    (sigma : Placement) (i : Fin 3) :
    (∑ h : ActiveOrder K tick sigma,
      ((populationLength (K := K) allocation 1 : ℝ) *
        AllFieldActiveLaws.orderMass allocation h) * workCapacity h.val.val.1 i) =
      (populationLength (K := K) allocation 1 : ℝ) *
        ((1 / 6 : ℝ) * FiniteSchedule.tickCapacity K nativeLA nativeLB
          (nativeLC (fun j => (allocation.mass j : ℝ))) tick i) := by
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, order_capacity_eq_native]

def physicalYield (K : ℕ) (allocation : Allocation) : ℝ :=
  ∑ tick ∈ Finset.range (K + 2), ∑ sigma : Placement,
    Staggering.minCapacity (physicalTickCapacity allocation tick
      (workCapacity (K := K)) sigma)

def scheduledYield (K : ℕ) (allocation : Fin 3 → ℝ) : ℝ :=
  ∑ tick ∈ Finset.range (K + 2), Staggering.minCapacity
    (FiniteSchedule.tickCapacity K nativeLA nativeLB (nativeLC allocation) tick)

theorem physicalYield_eq_scheduled (K : ℕ) (allocation : Allocation) :
    physicalYield K allocation = scheduledYield K (fun i => (allocation.mass i : ℝ)) := by
  unfold physicalYield scheduledYield
  apply Finset.sum_congr rfl
  intro tick htick
  rw [sum_physicalTick_minima, active_native_capacity]

theorem balanced_scheduledYield (K : ℕ) (hK : 2 ≤ K) (hgap : nativeB < nativeHigh) :
    scheduledYield K nativeLambda = (K : ℝ) * nativeCstar - nativeBeta :=
  FiniteSchedule.finite_schedule_yield K hK nativeLA nativeLB
    (nativeLC nativeLambda) nativeCstar (native_balanced hgap)

theorem nativeLC_tendsto {J : Type*} {filter : Filter J}
    {allocation : J → Fin 3 → ℝ} {limit : Fin 3 → ℝ}
    (h : ∀ i, Tendsto (fun j => allocation j i) filter (𝓝 (limit i))) (i : Fin 3) :
    Tendsto (fun j => nativeLC (allocation j) i) filter (𝓝 (nativeLC limit i)) := by
  simp_rw [nativeLC_expansion]
  exact tendsto_const_nhds.sub (((h i).const_mul 3).mul_const (nativeHigh - nativeB))

theorem tickCapacity_tendsto (K tick : ℕ) {J : Type*} {filter : Filter J}
    {allocation : J → Fin 3 → ℝ} {limit : Fin 3 → ℝ}
    (h : ∀ i, Tendsto (fun j => allocation j i) filter (𝓝 (limit i))) (i : Fin 3) :
    Tendsto (fun j => FiniteSchedule.tickCapacity K nativeLA nativeLB
      (nativeLC (allocation j)) tick i) filter
      (𝓝 (FiniteSchedule.tickCapacity K nativeLA nativeLB (nativeLC limit) tick i)) := by
  have hc : Tendsto (fun j => if FiniteSchedule.stageActive K tick 2 then
      nativeLC (allocation j) i else 0) filter
      (𝓝 (if FiniteSchedule.stageActive K tick 2 then nativeLC limit i else 0)) := by
    by_cases hh : FiniteSchedule.stageActive K tick 2
    · simpa only [hh, ite_true] using nativeLC_tendsto h i
    · simpa only [hh, ite_false] using (tendsto_const_nhds :
        Tendsto (fun _ : J => (0 : ℝ)) filter (𝓝 0))
  exact (tendsto_const_nhds.add tendsto_const_nhds).add hc

theorem scheduledYield_tendsto (K : ℕ) {J : Type*} {filter : Filter J}
    {allocation : J → Fin 3 → ℝ} {limit : Fin 3 → ℝ}
    (h : ∀ i, Tendsto (fun j => allocation j i) filter (𝓝 (limit i))) :
    Tendsto (fun j => scheduledYield K (allocation j)) filter
      (𝓝 (scheduledYield K limit)) := by
  unfold scheduledYield
  apply tendsto_finsetSum
  intro tick htick
  exact (tickCapacity_tendsto K tick h 0).min
    ((tickCapacity_tendsto K tick h 1).min (tickCapacity_tendsto K tick h 2))

theorem physicalYield_tendsto_balanced (K : ℕ) (hK : 2 ≤ K)
    (hgap : nativeB < nativeHigh) (allocation : ℕ → Allocation)
    (h : ∀ i, Tendsto (fun j => ((allocation j).mass i : ℝ)) atTop (𝓝 (nativeLambda i))) :
    Tendsto (fun j => physicalYield K (allocation j)) atTop
      (𝓝 ((K : ℝ) * nativeCstar - nativeBeta)) := by
  simp_rw [physicalYield_eq_scheduled]
  rw [← balanced_scheduledYield K hK hgap]
  exact scheduledYield_tendsto K h

theorem exists_balanced_allocation_sequence (hgap : nativeB < nativeHigh)
    (hfeas : ∀ i, nativeCstar - (nativeLA i + nativeLB i) < nativeHigh) :
    ∃ allocation : ℕ → Allocation,
      ∀ i, Tendsto (fun j => ((allocation j).mass i : ℝ)) atTop (𝓝 (nativeLambda i)) := by
  have hpos (i : Fin 3) : 0 < nativeLambda i :=
    Staggering.balanceFraction_pos nativeLA nativeLB nativeHigh nativeB hgap hfeas i
  let p : FiniteLaw (Fin 3) := {
    mass := nativeLambda
    nonneg := fun i => (hpos i).le
    total := Staggering.sum_balanceFraction nativeLA nativeLB nativeHigh nativeB hgap }
  obtain ⟨q, hq⟩ := ConditionalLabels.exists_rational_law_sequence p
  have he : ∀ᶠ j in atTop, ∀ i, 0 < (q j).toFiniteLaw.mass i :=
    Filter.eventually_all.mpr (fun i => (hq i).eventually_const_lt (hpos i))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  let allocation : ℕ → Allocation := fun j => {
    mass := (q (j + N)).mass
    positive := fun i => by
      have hi := hN (j + N) (by omega) i
      change (0 : ℝ) < ((q (j + N)).mass i : ℝ) at hi
      exact_mod_cast hi
    total := (q (j + N)).total }
  refine ⟨allocation, fun i => ?_⟩
  exact (hq i).comp (tendsto_add_atTop_nat N)

theorem exists_physicalYield_limit (K : ℕ) (hK : 2 ≤ K)
    (hgap : nativeB < nativeHigh)
    (hfeas : ∀ i, nativeCstar - (nativeLA i + nativeLB i) < nativeHigh) :
    ∃ allocation : ℕ → Allocation,
      Tendsto (fun j => physicalYield K (allocation j)) atTop
        (𝓝 ((K : ℝ) * nativeCstar - nativeBeta)) := by
  obtain ⟨allocation, ha⟩ := exists_balanced_allocation_sequence hgap hfeas
  exact ⟨allocation, physicalYield_tendsto_balanced K hK hgap allocation ha⟩

theorem initial_capacity (K : ℕ) :
    JointOrdinaryPopulationSelection.entropyRate (fun _ : Fin K => (1 : ℝ))
      (fun _ : Fin K => AllFieldInitialEntropy.orderedInitialLaw) -
    JointOrdinaryPopulationSelection.degreeRate (fun _ : Fin K => (1 : ℝ))
      (fun _ : Fin K => AllFieldInitialEntropy.orderedInitialLaw) =
        (K : ℝ) * AllFieldInitialEntropy.nativeH0 :=
  AllFieldInitialEntropy.ordinary_capacity_all_lots K

theorem initial_dilation_capacity (K : ℕ) (allocation : Allocation) :
    JointOrdinaryPopulationSelection.entropyRate
      (fun _ : Fin K => (populationLength (K := K) allocation 1 : ℝ))
      (fun _ : Fin K => AllFieldInitialEntropy.orderedInitialLaw) -
    JointOrdinaryPopulationSelection.degreeRate
      (fun _ : Fin K => (populationLength (K := K) allocation 1 : ℝ))
      (fun _ : Fin K => AllFieldInitialEntropy.orderedInitialLaw) =
        (populationLength (K := K) allocation 1 : ℝ) *
          ((K : ℝ) * AllFieldInitialEntropy.nativeH0) := by
  simp only [JointOrdinaryPopulationSelection.entropyRate,
    JointOrdinaryPopulationSelection.degreeRate, JointOrdinaryPopulationSelection.sideDegreeRate,
    AllFieldInitialEntropy.orderedInitialLaw_side_entropy, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, max_self]
  ring

end MatrixMultiplication.AllFieldScheduledYield

end

end OAI
