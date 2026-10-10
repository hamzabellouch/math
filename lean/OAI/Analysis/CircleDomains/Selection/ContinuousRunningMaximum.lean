import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.CompactOpen

namespace OAI

/-! A continuous running maximum for nonnegative continuous functions.
Using the norm of a curried map avoids any selection of maximizers. -/
open Set
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

def runningMaximum (k : C(unitInterval, ℝ)) : C(unitInterval, ℝ) :=
  let F : C(unitInterval × unitInterval, ℝ) :=
    ⟨fun p => k (min p.1 p.2), k.continuous.comp (continuous_fst.min continuous_snd)⟩
  ⟨fun t => ‖F.curry t‖, continuous_norm.comp F.curry.continuous⟩

lemma runningMaximum_nonneg (k : C(unitInterval, ℝ)) (t : unitInterval) :
    0 ≤ runningMaximum k t := by
  dsimp only [runningMaximum, ContinuousMap.coe_mk]
  exact norm_nonneg _

lemma le_runningMaximum (k : C(unitInterval, ℝ)) {s t : unitInterval} (hst : s ≤ t) :
    k s ≤ runningMaximum k t := by
  let F : C(unitInterval × unitInterval, ℝ) :=
    ⟨fun p => k (min p.1 p.2), k.continuous.comp (continuous_fst.min continuous_snd)⟩
  have hh := (F.curry t).norm_coe_le_norm s
  change ‖k (min t s)‖ ≤ runningMaximum k t at hh
  rw [min_eq_right hst, Real.norm_eq_abs] at hh
  exact (le_abs_self _).trans hh

lemma runningMaximum_le (k : C(unitInterval, ℝ)) (hk : ∀ u, 0 ≤ k u)
    {t : unitInterval} {c : ℝ} (hc : 0 ≤ c) (h : ∀ u ≤ t, k u ≤ c) :
    runningMaximum k t ≤ c := by
  apply (ContinuousMap.norm_le _ hc).mpr
  intro u
  change ‖k (min t u)‖ ≤ c
  rw [Real.norm_eq_abs, abs_of_nonneg (hk _)]
  exact h _ (min_le_left _ _)

lemma runningMaximum_mono (k : C(unitInterval, ℝ)) (hk : ∀ u, 0 ≤ k u) :
    Monotone (runningMaximum k) := by
  intro s t hst
  exact runningMaximum_le k hk (runningMaximum_nonneg k t)
    (fun u hu => le_runningMaximum k (hu.trans hst))

lemma runningMaximum_eq_of_constant (k : C(unitInterval, ℝ)) (hk : ∀ u, 0 ≤ k u)
    {s t : unitInterval} (hst : s ≤ t) (heq : ∀ u ∈ Icc s t, k u = k s) :
    runningMaximum k s = runningMaximum k t := by
  apply le_antisymm (runningMaximum_mono k hk hst)
  apply runningMaximum_le k hk (runningMaximum_nonneg k s)
  intro u hut
  by_cases hus : u ≤ s
  · exact le_runningMaximum k hus
  · rw [heq u ⟨le_of_not_ge hus, hut⟩]
    exact le_runningMaximum k le_rfl

end CircleDomainRigidity

end

end OAI
