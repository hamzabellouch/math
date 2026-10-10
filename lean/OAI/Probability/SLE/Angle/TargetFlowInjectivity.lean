import OAI.Probability.SLE.Angle.TargetFlowMeasurability

namespace OAI

/-! The raw cutoff construction retains injectivity on the surviving
domain. This is used to construct its inverse as a measurable map. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma cutoffFlow_injective (κ : ℝ) (b : Driver) (j : ℕ) (hj : 1 ≤ j)
    (T : ℝ) (hT : 0 ≤ T) : Function.Injective (fun z => cutoffFlow κ b j z T) := by
  intro z w he
  obtain ⟨L,K,hL,hK⟩ := cutoffField_bounds κ j hj
  have hd (z : ℂ) (t : ℝ) (ht : t ∈ Ioc 0 T) :
      HasDerivWithinAt (cutoffFlow κ b j z)
        (cutoffField κ b j t (cutoffFlow κ b j z t)) (Iic t) t :=
    ((cutoffFlow_hasDerivWithinAt κ b j hj z t ht.1.le).hasDerivAt
      (Ici_mem_nhds ht.1)).hasDerivWithinAt
  have heq := ODE_solution_unique_of_mem_Icc_left (s := fun _ => univ)
    (fun t _ => (hK b t).lipschitzOnWith)
    ((cutoffFlow_continuousOn κ b j hj z).mono Icc_subset_Ici_self) (hd z)
    (fun _ _ => mem_univ _) ((cutoffFlow_continuousOn κ b j hj w).mono Icc_subset_Ici_self)
    (hd w) (fun _ _ => mem_univ _) he
  have hz := heq (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)
  simpa only [cutoffFlow_zero κ b j hj] using hz

lemma surviving_common_cutoff
    (κ : ℝ) (b : Driver) (z : ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hs : Surviving κ b z T) (j : ℕ) (hj : Nat.find hs ≤ j) :
    cutoffFlow κ b j z T = flow κ b z T := by
  let k := Nat.find hs
  have hk : 1 ≤ k := (Nat.find_spec hs).1
  have hj' : 1 ≤ j := hk.trans hj
  have hinv : (j:ℝ)⁻¹ ≤ (k:ℝ)⁻¹ :=
    inv_anti₀ (by exact_mod_cast (Nat.succ_le_iff.mp hk) : (0:ℝ)<k)
      (by exact_mod_cast hj)
  have hheight := surviving_cutoff_height κ b z T k hk (Nat.find_spec hs).2
  have hderiv (t : ℝ) (ht : t ∈ Ico 0 T) :
      HasDerivWithinAt (cutoffFlow κ b k z)
        ((a κ:ℂ)/(cutoffFlow κ b k z t-driverValue b t)) (Ici t) t := by
    have h := (cutoffFlow_hasDerivWithinAt κ b k hk z t ht.1).mono
      (Ici_subset_Ici.mpr ht.1)
    rw [cutoffField_eq_reciprocal κ b k t _
      (cutoff_inactive_of_height k hk _ _ (hheight t (Ico_subset_Icc_self ht)).le)] at h
    exact h
  have he := cutoffFlow_eq_of_positive_trajectory κ b j hj' z T hT
    (cutoffFlow κ b k z) ((cutoffFlow_continuousOn κ b k hk z).mono Icc_subset_Ici_self)
    (cutoffFlow_zero κ b k hk z)
    (fun t ht => hinv.trans (hheight t ht).le) hderiv T ⟨hT,le_rfl⟩
  simpa only [flow,dite_eq_left hs] using he

lemma flow_injOn_surviving (κ : ℝ) (b : Driver) (T : ℝ) (hT : 0 ≤ T) :
    InjOn (fun z => flow κ b z T) {z | Surviving κ b z T} := by
  intro z hz w hw he
  let j := max (Nat.find hz) (Nat.find hw)
  have hj : 1 ≤ j := (Nat.find_spec hz).1.trans (le_max_left _ _)
  apply cutoffFlow_injective κ b j hj T hT
  change cutoffFlow κ b j z T = cutoffFlow κ b j w T
  rw [surviving_common_cutoff κ b z T hT hz j (le_max_left _ _),
    surviving_common_cutoff κ b w T hT hw j (le_max_right _ _)]
  exact he

end SLEExactGauge.Target

end

end OAI
