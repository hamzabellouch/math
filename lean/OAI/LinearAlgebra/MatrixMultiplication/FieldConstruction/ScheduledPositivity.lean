import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ScheduledYield
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialGibbs

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldScheduledPositivity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldInitialEntropy AllFieldNativeCapacity AllFieldScheduledYield Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

theorem nativeH0_pos : 0 < nativeH0 := by
  let p := orderedInitialLaw.map (JointPopulation.shapeSide 0)
  have hzero : 0 < p.mass 0 := by
    have hp := AllFieldInitialGibbs.orderedInitialLaw_positive
      ((0 : Fin 17), (0 : Fin 17), (16 : Fin 17)) (by decide)
    exact hp.trans_le (orderedInitialLaw.mass_le_map_mass
      (JointPopulation.shapeSide 0) ((0 : Fin 17), (0 : Fin 17), (16 : Fin 17)))
  have hone : 0 < p.mass 1 := by
    have hp := AllFieldInitialGibbs.orderedInitialLaw_positive
      ((1 : Fin 17), (0 : Fin 17), (15 : Fin 17)) (by decide)
    exact hp.trans_le (orderedInitialLaw.mass_le_map_mass
      (JointPopulation.shapeSide 0) ((1 : Fin 17), (0 : Fin 17), (15 : Fin 17)))
  have hpair : p.mass 0 + p.mass 1 ≤ 1 := by
    have hs : (∑ k ∈ ({0, 1} : Finset (Fin 17)), p.mass k) ≤
        ∑ k : Fin 17, p.mass k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => p.nonneg k)
    simpa [p.total] using hs
  have hterm : 0 < entropyTerm (p.mass 0) :=
    mul_pos_of_neg_of_neg (neg_neg_of_pos hzero) (Real.log_neg hzero (by linarith))
  have hentropy : 0 < finiteEntropy p.mass := hterm.trans_le
    (Finset.single_le_sum
      (fun k _ => entropyTerm_nonneg (p.nonneg k) (p.mass_le_one k))
      (Finset.mem_univ 0))
  rw [← orderedInitialLaw_side_entropy 0]
  have hm : p.mass = JointPopulationRates.sideMass orderedInitialLaw.mass 0 := by
    funext k
    simp only [p, FiniteLaw.map_mass, JointPopulationRates.sideMass]
  rw [← hm]
  exact hentropy

theorem initial_capacity_pos (K : ℕ) (hK : 0 < K) :
    0 < (K : ℝ) * nativeH0 := mul_pos (Nat.cast_pos.mpr hK) nativeH0_pos

theorem tickCapacity_pos (K tick : ℕ) (hK : 2 ≤ K) (htick : tick < K + 2)
    (a b c : Staggering.Capacity)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : Fin 3) : 0 < FiniteSchedule.tickCapacity K a b c tick i := by
  have hA := ha i
  have hB := hb i
  have hC := hc i
  unfold FiniteSchedule.tickCapacity
  split_ifs <;> first
    | positivity
    | (simp only [FiniteSchedule.stageActive, Fin.val_zero, Fin.val_one] at *; omega)

theorem physical_order_capacity_pos (K tick : ℕ) (hK : 2 ≤ K)
    (htick : tick < K + 2) (allocation : Allocation) (sigma : Placement)
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC (fun j => (allocation.mass j : ℝ)) i) :
    0 < Staggering.minCapacity
      (physicalTickCapacity allocation tick (workCapacity (K := K)) sigma) := by
  rw [physical_order_native_capacity, PhysicalOrders.minCapacity_mul _ _ (by norm_num)]
  exact mul_pos (by norm_num) (Staggering.minCapacity_pos _
    (tickCapacity_pos K tick hK htick _ _ _ ha hb hc))

theorem eventually_physical_order_capacity_pos (K : ℕ) (hK : 2 ≤ K)
    (allocation : ℕ → Allocation)
    (h : ∀ i, Tendsto (fun j => ((allocation j).mass i : ℝ)) atTop (𝓝 (nativeLambda i)))
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC nativeLambda i) :
    ∀ᶠ j in atTop, ∀ tick < K + 2, ∀ sigma : Placement,
      0 < Staggering.minCapacity
        (physicalTickCapacity (allocation j) tick (workCapacity (K := K)) sigma) := by
  have he : ∀ᶠ j in atTop, ∀ i,
      0 < nativeLC (fun k => ((allocation j).mass k : ℝ)) i :=
    Filter.eventually_all.mpr fun i => (nativeLC_tendsto h i).eventually_const_lt (hc i)
  filter_upwards [he] with j hj
  exact fun tick htick sigma =>
    physical_order_capacity_pos K tick hK htick (allocation j) sigma ha hb hj

end MatrixMultiplication.AllFieldScheduledPositivity

end

end OAI
