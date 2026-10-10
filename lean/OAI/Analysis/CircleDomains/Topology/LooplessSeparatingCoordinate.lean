import OAI.Analysis.CircleDomains.Topology.LooplessTimeCoordinate

namespace OAI

/-! A single continuous monotone real coordinate with exactly the fibers
of a loopless metric path. -/
open Set Function Metric TopologicalSpace
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

def looplessCoordinateTerm (g : C(unitInterval, X)) (n : ℕ) : C(unitInterval, ℝ) :=
  ⟨fun t => (1 / 2 : ℝ)^n * runningMaximum (prefixDistance g (denseSeq unitInterval n)) t,
    continuous_const.mul (runningMaximum _).continuous⟩

lemma looplessCoordinateTerm_nonneg (g : C(unitInterval, X)) (n : ℕ) (t : unitInterval) :
    0 ≤ looplessCoordinateTerm g n t :=
  mul_nonneg (by positivity) (runningMaximum_nonneg _ _)

lemma looplessCoordinateTerm_le (g : C(unitInterval, X)) (n : ℕ) (t : unitInterval) :
    looplessCoordinateTerm g n t ≤ (1 / 2 : ℝ)^n := by
  apply (mul_le_mul_of_nonneg_left _ (by positivity)).trans_eq (mul_one _)
  exact runningMaximum_le _ (prefixDistance_nonneg _ _) zero_le_one
    (fun u _ => prefixDistance_le_one _ _ u)

lemma summable_looplessCoordinateTerm (g : C(unitInterval, X)) (t : unitInterval) :
    Summable (fun n => looplessCoordinateTerm g n t) :=
  Summable.of_nonneg_of_le (fun n => looplessCoordinateTerm_nonneg g n t)
    (fun n => looplessCoordinateTerm_le g n t) summable_geometric_two

def looplessCoordinate (g : C(unitInterval, X)) : C(unitInterval, ℝ) where
  toFun t := ∑' n, looplessCoordinateTerm g n t
  continuous_toFun := by
    apply continuous_tsum (fun n => (looplessCoordinateTerm g n).continuous) summable_geometric_two
    intro n t
    rw [Real.norm_eq_abs, abs_of_nonneg (looplessCoordinateTerm_nonneg g n t)]
    exact looplessCoordinateTerm_le g n t

lemma looplessCoordinate_mono (g : C(unitInterval, X)) : Monotone (looplessCoordinate g) := by
  intro s t hst
  exact Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left
      (runningMaximum_mono _ (prefixDistance_nonneg _ _) hst) (by positivity))
    (summable_looplessCoordinateTerm g s) (summable_looplessCoordinateTerm g t)

lemma looplessCoordinate_eq_of_eq (g : C(unitInterval, X))
    (hloop : ∀ s t : unitInterval, s ≤ t → g s = g t → ∀ u ∈ Icc s t, g u = g s)
    {s t : unitInterval} (heq : g s = g t) : looplessCoordinate g s = looplessCoordinate g t := by
  wlog hst : s ≤ t generalizing s t
  · exact (this heq.symm (le_of_not_ge hst)).symm
  apply tsum_congr
  intro n
  change (1 / 2 : ℝ)^n * _ = (1 / 2 : ℝ)^n * _
  rw [prefixRunning_eq_of_loop g hloop _ hst heq]

lemma looplessCoordinate_lt_of_ne (g : C(unitInterval, X))
    (hloop : ∀ s t : unitInterval, s ≤ t → g s = g t → ∀ u ∈ Icc s t, g u = g s)
    {s t : unitInterval} (hst : s ≤ t) (hne : g s ≠ g t) :
    looplessCoordinate g s < looplessCoordinate g t := by
  have hlt : s < t := lt_of_le_of_ne hst (fun h => hne (congrArg g h))
  obtain ⟨n, hsn, hnt, hne'⟩ := dense_prefix_separates g hlt hne
  have hle : ∀ k, looplessCoordinateTerm g k s ≤ looplessCoordinateTerm g k t :=
    fun k => mul_le_mul_of_nonneg_left
      (runningMaximum_mono _ (prefixDistance_nonneg _ _) hst) (by positivity)
  have hterm : looplessCoordinateTerm g n s < looplessCoordinateTerm g n t := by
    change (1 / 2 : ℝ)^n * _ < (1 / 2 : ℝ)^n * _
    apply mul_lt_mul_of_pos_left _ (by positivity)
    rw [prefixRunning_eq_zero g hsn.le]
    exact (prefixDistance_pos g hloop hnt.le hne').trans_le (le_runningMaximum _ le_rfl)
  exact Summable.tsum_lt_tsum hle hterm
    (summable_looplessCoordinateTerm g s) (summable_looplessCoordinateTerm g t)

lemma looplessCoordinate_fibers (g : C(unitInterval, X))
    (hloop : ∀ s t : unitInterval, s ≤ t → g s = g t → ∀ u ∈ Icc s t, g u = g s)
    (s t : unitInterval) : looplessCoordinate g s = looplessCoordinate g t ↔ g s = g t := by
  constructor
  · intro h
    by_contra hne
    rcases le_total s t with hst | hts
    · exact (looplessCoordinate_lt_of_ne g hloop hst hne).ne h
    · exact (looplessCoordinate_lt_of_ne g hloop hts (Ne.symm hne)).ne h.symm
  · exact looplessCoordinate_eq_of_eq g hloop

end CircleDomainRigidity

end

end OAI
