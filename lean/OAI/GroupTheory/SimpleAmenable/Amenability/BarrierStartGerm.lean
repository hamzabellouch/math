import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FullGroupAffineData
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierAlgorithm

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BarrierStartGerm
open Classical Set

theorem continuous_nonzero_sign {X : Type*} [TopologicalSpace X] {C : Set X}
    (hC : IsPreconnected C) {f : X → ℝ} (hf : ContinuousOn f C)
    (hn : ∀x ∈ C,f x ≠ 0) {x y : X} (hx : x ∈ C) (hy : y ∈ C) :
    f x < 0 ↔ f y < 0 := by
  have h (u v : X) (hu : u ∈ C) (hv : v ∈ C) (hu' : f u < 0) : f v < 0 := by
    by_contra hh
    obtain ⟨z,hz,hz0⟩ := hC.intermediate_value hu hv hf ⟨hu'.le,le_of_not_gt hh⟩
    exact hn z hz hz0
  exact ⟨h x y hx hy,h y x hy hx⟩

theorem barrier_cut_difference (a : ℕ) (j k : Fin 4) (c : CutRing) (s t : ℝ) :
    cutForm a k (barrierLinePoint a j c t)=cutForm a k (barrierLinePoint a j c s)+
      (t-s)*cutForm a k (barrierTangent a j) := by
  have hh := barrierLinePoint_sub a j c t s
  have hp : barrierLinePoint a j c t=barrierLinePoint a j c s+(t-s) • barrierTangent a j := by
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  rw [hp,cutForm_add,cutForm_smul]

theorem barrier_start_cut_sign {a : ℕ} (ha : 0 < a) (j k : Fin 4) (c d : CutRing)
    {L U s x : ℝ} (hs : s ∈ Ico L U) (hx : x ∈ Ioo L U)
    (hn : ∀r ∈ Ioo L U,cutForm a k (barrierLinePoint a j c r) ≠ ordinary d) :
    (if cutForm a k (barrierLinePoint a j c s)=ordinary d then
      cutForm a k (barrierFlagDirection ha j) < 0 else
      cutForm a k (barrierLinePoint a j c s) < ordinary d) ↔
      cutForm a k (barrierLinePoint a j c x) < ordinary d := by
  let t := (s+U)/2
  have hst : s < t := by dsimp [t]; linarith [hs.2]
  have ht : t ∈ Ioo L U := by dsimp [t]; constructor <;> linarith [hs.1,hs.2]
  let f := fun r => cutForm a k (barrierLinePoint a j c r)-ordinary d
  have hf : Continuous f := ((cutForm_continuous a k).comp (barrierLinePoint_continuous a j c)).sub continuous_const
  have hnon : ∀r ∈ Ioo L U,f r ≠ 0 := fun r hr => sub_ne_zero.mpr (hn r hr)
  have htx : f t < 0 ↔ f x < 0 := continuous_nonzero_sign isPreconnected_Ioo hf.continuousOn hnon ht hx
  have hdif := barrier_cut_difference a j k c s t
  by_cases he : cutForm a k (barrierLinePoint a j c s)=ordinary d
  · have hB : cutForm a k (barrierTangent a j) ≠ 0 := by
      intro hh
      apply hn t ht
      rw [he,hh,mul_zero,add_zero] at hdif
      exact hdif
    have hflag := (barrierFlagDirection_spec ha j).2.2.2 k
    rw [ite_eq_right hB] at hflag
    rw [ite_eq_left he,hflag]
    have heq : f t=(t-s)*cutForm a k (barrierTangent a j) := by dsimp [f]; linarith
    have hsign : f t < 0 ↔ cutForm a k (barrierTangent a j) < 0 := by
      rw [heq,mul_neg_iff]
      have hts : 0 < t-s := sub_pos.mpr hst
      simp [hts,not_lt_of_gt hts]
    exact (hsign.symm.trans htx).trans (sub_lt_zero (a:=cutForm a k (barrierLinePoint a j c x)) (b:=ordinary d))
  · rw [ite_eq_right he]
    have hseg : ∀r ∈ Icc s t,f r ≠ 0 := by
      intro r hr
      by_cases hrs : r=s
      · subst r
        exact sub_ne_zero.mpr he
      · exact hnon r ⟨lt_of_le_of_lt hs.1 (lt_of_le_of_ne hr.1 (Ne.symm hrs)),hr.2.trans_lt ht.2⟩
    have hsign := continuous_nonzero_sign isPreconnected_Icc hf.continuousOn hseg
      (left_mem_Icc.mpr hst.le) (right_mem_Icc.mpr hst.le)
    simpa only [f,sub_lt_zero] using hsign.trans htx

theorem flagValue_of_arrangement_signs {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) → f p=f q)
    (z : SquareFlag a v) (p : GenericSquare a)
    (hs : ∀l ∈ T,(if cutForm a l.1 z.val=ordinary l.2 then cutForm a l.1 v < 0
      else cutForm a l.1 z.val < ordinary l.2) ↔ cutForm a l.1 p.val < ordinary l.2) :
    flagValue f ⟨T,hT⟩ z=f p := by
  apply flagValue_eq
  refine ⟨arrangementNeighborhood a T z.val,arrangementNeighborhood_open a T z.val,
    self_mem_arrangementNeighborhood a T z.val,?_⟩
  intro q hq hqv
  apply hT q p
  intro l hl
  have hh := planeSign_neighborhood (p:=⟨q.val,q.property.2.2⟩) hq hqv hl
  change squareSign l q=_ at hh
  rw [hh]
  exact decide_eq_decide.mpr (hs l hl)

theorem flagAffineData_barrier_chart {a m : ℕ} (ha : 0 < a) (g : polygonFullGroup a m)
    (i : Fin m) (j : Fin 4) (c : CutRing) (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q)
    (p : GenericSquare a) {L U s : ℝ} (hLU : L < U) (hs : s ∈ Ico L U)
    (hchart : ∀l ∈ T,∀r ∈ Ioo L U,
      cutForm a l.1 (barrierLinePoint a j c r) ≠ ordinary l.2 ∧
      (cutForm a l.1 (barrierLinePoint a j c r) < ordinary l.2 ↔
        cutForm a l.1 p.val < ordinary l.2))
    (z : SquareFlag a (barrierFlagDirection ha j)) (hz : z.val=barrierLinePoint a j c s) :
    flagAffineData g i z=fullGroupAffineData g i p := by
  let x := (L+U)/2
  have hx : x ∈ Ioo L U := by dsimp [x]; constructor <;> linarith
  apply flagValue_of_arrangement_signs (fullGroupAffineData g i) T hT z p
  intro l hl
  rw [hz]
  exact (barrier_start_cut_sign ha j l.1 c l.2 hs hx
    (fun r hr => (hchart l hl r hr).1)).trans (hchart l hl x hx).2

end BarrierStartGerm

end SimpleAmenable
end
end

end OAI
