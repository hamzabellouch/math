import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Linarith

namespace OAI

/-! Removing a closed loop preserves every modulus of continuity and
cannot increase the diameter on any parameter interval. -/
open Set Function Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
variable {a b : unitInterval}

def erasePathLoop (g : C(unitInterval, X)) (a b : unitInterval)
    (hab : a ≤ b) (heq : g a = g b) : C(unitInterval, X) where
  toFun := (Iic b).piecewise (fun t => g (min t a)) g
  continuous_toFun := by
    apply Continuous.piecewise _ (g.continuous.comp (continuous_id.min continuous_const))
      g.continuous
    intro t ht
    have ht' : t = b := by
      have h := frontier_Iic_subset b ht
      simpa only [mem_singleton_iff] using h
    subst t
    change g (min b a) = g b
    simpa only [min_eq_right hab] using heq

lemma erasePathLoop_of_le (g : C(unitInterval, X)) (hab : a ≤ b) (heq : g a = g b)
    {t : unitInterval} (ht : t ≤ a) : erasePathLoop g a b hab heq t = g t := by
  simp [erasePathLoop, ht.trans hab, min_eq_left ht]

lemma erasePathLoop_of_mem (g : C(unitInterval, X)) (hab : a ≤ b) (heq : g a = g b)
    {t : unitInterval} (ht : t ∈ Icc a b) : erasePathLoop g a b hab heq t = g a := by
  simp [erasePathLoop, ht.2, min_eq_right ht.1]

lemma erasePathLoop_of_ge (g : C(unitInterval, X)) (hab : a ≤ b) (heq : g a = g b)
    {t : unitInterval} (ht : b ≤ t) : erasePathLoop g a b hab heq t = g t := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [erasePathLoop_of_mem g hab heq ⟨hab, le_rfl⟩] using heq
  · simp [erasePathLoop, ht.not_ge]

lemma erasePathLoop_pair (g : C(unitInterval, X)) (hab : a ≤ b) (heq : g a = g b)
    {s t : unitInterval} (hst : s ≤ t) :
    erasePathLoop g a b hab heq s = erasePathLoop g a b hab heq t ∨
    ∃ u ∈ Icc s t, ∃ v ∈ Icc s t,
      erasePathLoop g a b hab heq s = g u ∧ erasePathLoop g a b hab heq t = g v := by
  by_cases hsa : s ≤ a
  · have hs := erasePathLoop_of_le g hab heq hsa
    by_cases hta : t ≤ a
    · exact Or.inr ⟨s, ⟨le_rfl, hst⟩, t, ⟨hst, le_rfl⟩, hs,
        erasePathLoop_of_le g hab heq hta⟩
    by_cases htb : t ≤ b
    · exact Or.inr ⟨s, ⟨le_rfl, hst⟩, a, ⟨hsa, le_of_not_ge hta⟩, hs,
        erasePathLoop_of_mem g hab heq ⟨le_of_not_ge hta, htb⟩⟩
    · exact Or.inr ⟨s, ⟨le_rfl, hst⟩, t, ⟨hst, le_rfl⟩, hs,
        erasePathLoop_of_ge g hab heq (le_of_not_ge htb)⟩
  by_cases hsb : s ≤ b
  · have hs := erasePathLoop_of_mem g hab heq ⟨le_of_not_ge hsa, hsb⟩
    by_cases htb : t ≤ b
    · exact Or.inl (hs.trans (erasePathLoop_of_mem g hab heq
        ⟨(le_of_not_ge hsa).trans hst, htb⟩).symm)
    · exact Or.inr ⟨b, ⟨hsb, le_of_not_ge htb⟩, t, ⟨hst, le_rfl⟩,
        hs.trans heq, erasePathLoop_of_ge g hab heq (le_of_not_ge htb)⟩
  · exact Or.inr ⟨s, ⟨le_rfl, hst⟩, t, ⟨hst, le_rfl⟩,
      erasePathLoop_of_ge g hab heq (le_of_not_ge hsb),
      erasePathLoop_of_ge g hab heq ((le_of_not_ge hsb).trans hst)⟩

lemma unitInterval_dist_le_of_mem_Icc {s t u v : unitInterval}
    (hu : u ∈ Icc s t) (hv : v ∈ Icc s t) : dist u v ≤ dist s t := by
  change |(u : ℝ) - v| ≤ |(s : ℝ) - t|
  have hu₁ : (s : ℝ) ≤ u := hu.1
  have hu₂ : (u : ℝ) ≤ t := hu.2
  have hv₁ : (s : ℝ) ≤ v := hv.1
  have hv₂ : (v : ℝ) ≤ t := hv.2
  rw [abs_of_nonpos (show (s : ℝ) - t ≤ 0 by linarith)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end CircleDomainRigidity

end

end OAI
