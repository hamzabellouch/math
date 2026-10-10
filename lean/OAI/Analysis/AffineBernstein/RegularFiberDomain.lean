import Mathlib
import OAI.Analysis.AffineBernstein.TubeCombination
import OAI.Analysis.AffineBernstein.NormalizedCaps

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section RegularFiberDomain
open Metric Filter

/-- The largest open positive base domain on which the literal transverse
fibers are compact and contain zero in their interiors. It is defined directly
from the convex body's fibers, without any estimate or derivative hypothesis. -/
def regularPositiveFiberDomain {k m : ℕ} (C : Set (Space k × Space m)) : Set (Space k) :=
  {s | ∃ U : Set (Space k), IsOpen U ∧ U ⊆ positiveOrthant k ∧ s ∈ U ∧
    ∀ t ∈ U, IsCompact (modelFiber C t) ∧ (0:Space m) ∈ interior (modelFiber C t)}

lemma regularPositiveFiberDomain_isOpen {k m : ℕ} (C : Set (Space k × Space m)) :
    IsOpen (regularPositiveFiberDomain C) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro s ⟨U,hU,hpos,hs,hreg⟩
  apply Filter.mem_of_superset (hU.mem_nhds hs)
  intro t ht
  exact ⟨U,hU,hpos,ht,hreg⟩

lemma regularPositiveFiberDomain_positive {k m : ℕ} (C : Set (Space k × Space m)) :
    regularPositiveFiberDomain C ⊆ positiveOrthant k := by
  rintro s ⟨_,_,hpos,hs,_⟩
  exact hpos hs

lemma regularPositiveFiberDomain_compact {k m : ℕ} (C : Set (Space k × Space m))
    {s : Space k} (hs : s ∈ regularPositiveFiberDomain C) : IsCompact (modelFiber C s) := by
  obtain ⟨_,_,_,hs,hreg⟩ := hs
  exact (hreg s hs).1

lemma regularPositiveFiberDomain_zero {k m : ℕ} (C : Set (Space k × Space m))
    {s : Space k} (hs : s ∈ regularPositiveFiberDomain C) :
    (0:Space m) ∈ interior (modelFiber C s) := by
  obtain ⟨_,_,_,hs,hreg⟩ := hs
  exact (hreg s hs).2

lemma openBox_subset_regularPositiveFiberDomain {k m : ℕ}
    {C : Set (Space k × Space m)} (hC : IsClosed C) {a b R : ℝ} (ha : 0 < a)
    (hreg : ∀ s : Space k, (∀ i, s i ∈ Icc a b) →
      (0:Space m) ∈ interior (modelFiber C s) ∧ modelFiber C s ⊆ closedBall 0 R) :
    {s : Space k | ∀ i, a < s i ∧ s i < b} ⊆ regularPositiveFiberDomain C := by
  intro s hs
  refine ⟨{s : Space k | ∀ i, a < s i ∧ s i < b},?_,?_,hs,?_⟩
  · rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite fun i => ?_
    exact (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).inter
      (isOpen_lt (EuclideanSpace.proj i).continuous continuous_const)
  · intro t ht i
    exact ha.trans (ht i).1
  · intro t ht
    have hh := hreg t (fun i => ⟨(ht i).1.le,(ht i).2.le⟩)
    refine ⟨(isCompact_closedBall _ _).of_isClosed_subset ?_ hh.2,hh.1⟩
    exact hC.preimage (continuous_const.prodMk continuous_id)

/-- Closed logarithmic boxes agree exactly with the source definition. -/
def logarithmicBox (k : ℕ) (L : ℝ) : Set (Space k) := {x | ∀ i, |x i| ≤ L}

/-- Every fixed logarithmic box is eventually available in a normalized-model
approximation. The regular domains are produced from the actual fibers. -/
theorem LocalDistanceConverges.eventually_regular_logBox
    {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}
    (h : LocalDistanceConverges Cj C) (hC : IsModelShape C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {r R : ℝ} (hr : 0 < r)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R)
    (T : ℕ) : ∀ᶠ j in atTop,
      logarithmicBox k T ⊆ logSpace '' regularPositiveFiberDomain (Cj j) := by
  have ha : 0 < Real.exp (-(T:ℝ)-1) := Real.exp_pos _
  have ha1 : Real.exp (-(T:ℝ)-1) ≤ 1 := Real.exp_le_one_iff.mpr (by have : (0:ℝ) ≤ T := Nat.cast_nonneg T; linarith)
  have hb : 1 ≤ Real.exp ((T:ℝ)+1) := Real.one_le_exp_iff.mpr (by positivity)
  have hh := h.eventually_normalized_fibers hC hclj hcvj hnej hr ha ha1 hb hin hout
  filter_upwards [hh] with j hj
  intro t ht
  refine ⟨expSpace t,?_,logSpace_expSpace t⟩
  apply openBox_subset_regularPositiveFiberDomain (hclj j) ha
    (fun s hs => (hj s hs).2)
  intro i
  obtain ⟨hl,hu⟩ := abs_le.mp (ht i)
  change Real.exp (-(T:ℝ)-1) < Real.exp (t i) ∧ Real.exp (t i) < Real.exp ((T:ℝ)+1)
  exact ⟨Real.exp_lt_exp.mpr (by linarith),Real.exp_lt_exp.mpr (by linarith)⟩
end RegularFiberDomain

end AffineBernstein
end

end OAI
