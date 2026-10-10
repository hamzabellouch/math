import OAI.Probability.SwitchChain.PairEqualityProjection
import OAI.Probability.SwitchChain.PairProjectionCell

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def gatedCentered (i j k l : Fin n) : StateSpace n d :=
  WithLp.toLp 2 (fun G => if active i j k l G then centered i j k l G else 0)

theorem gatedCentered_mem (i j k l : Fin n) (hij : i ≠ j) :
    gatedCentered (d := d) i j k l ∈ equalitySpace i j k l := by
  intro G
  refine ⟨1, fun H h => ?_⟩
  have ha := active_sameFiber i j k l hij h
  change (if active i j k l H then _ else 0) = _
  simp only [one_mul, ha]

theorem restrictCell_mem (i j k l : Fin n)
    (C : GraphState n d → Prop) (hC : CellInvariant {i,j} C)
    (f : StateSpace n d) (hf : f ∈ equalitySpace i j k l) :
    restrictCell C f ∈ equalitySpace i j k l := by
  intro G
  obtain ⟨c,hc⟩ := hf G
  refine ⟨if C G then c else 0, fun H h => ?_⟩
  rw [restrictCell_apply, ← hC G H h]
  by_cases hG : C G
  · simpa only [ite_eq_left hG] using hc H h
  · simp only [ite_eq_right hG, zero_mul]

theorem fiberCell_invariant (a : Finset (Fin n)) (G : GraphState n d) :
    CellInvariant a (fun H : GraphState n d => SameFiber a G.val H.val) := by
  intro H K h
  exact ⟨fun hG => hG.trans h, fun hG => hG.trans h.symm⟩

def localizedVector (i j k l : Fin n) (G : GraphState n d) : StateSpace n d :=
  restrictCell (fun H => SameFiber {i,j} G.val H.val) (gatedCentered i j k l)

theorem localizedVector_mem (i j k l : Fin n) (hij : i ≠ j) (G : GraphState n d) :
    localizedVector i j k l G ∈ equalitySpace i j k l :=
  restrictCell_mem i j k l _ (fiberCell_invariant _ G) _
    (gatedCentered_mem i j k l hij)

theorem restrict_eq_smul_localizedVector (i j k l : Fin n) (hij : i ≠ j)
    (G : GraphState n d) (f : StateSpace n d) (hf : f ∈ equalitySpace i j k l) :
    ∃ c : ℝ, restrictCell (fun H => SameFiber {i,j} G.val H.val) f =
      c • localizedVector i j k l G := by
  obtain ⟨c,hc⟩ := hf G
  refine ⟨c, ?_⟩
  ext H
  by_cases h : SameFiber {i,j} G.val H.val
  · change (if SameFiber {i,j} G.val H.val then f H else 0) =
      c * (if SameFiber {i,j} G.val H.val then gatedCentered i j k l H else 0)
    rw [ite_eq_left h, ite_eq_left h, hc H h]
    change c * (if active i j k l G then _ else 0) =
      c * (if active i j k l H then _ else 0)
    rw [active_sameFiber i j k l hij h]
  · simp [restrictCell, localizedVector, h]

theorem projection_localization (i j k l : Fin n) (hij : i ≠ j)
    (G : GraphState n d) (f : StateSpace n d) :
    (Submodule.span ℝ {localizedVector i j k l G}).starProjection f =
      restrictCell (fun H => SameFiber {i,j} G.val H.val) (projection i j k l f) := by
  let z := localizedVector i j k l G
  let P := Submodule.span ℝ {z}
  have hz : z ∈ equalitySpace i j k l := localizedVector_mem i j k l hij G
  have hr : projection i j k l f ∈ equalitySpace i j k l :=
    (equalitySpace i j k l).starProjection_apply_mem f
  obtain ⟨c,hc⟩ := restrict_eq_smul_localizedVector i j k l hij G _ hr
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [hc]
    exact Submodule.smul_mem P c (Submodule.subset_span (Set.mem_singleton z))
  · intro w hw
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hw
    rw [← ht, inner_smul_right]
    suffices hzero : ⟪f - restrictCell (fun H => SameFiber {i,j} G.val H.val)
        (projection i j k l f), z⟫ = 0 by rw [hzero, mul_zero]
    have horth := (equalitySpace i j k l).starProjection_inner_eq_zero f z hz
    change ⟪f - projection i j k l f, z⟫ = 0 at horth
    rw [← horth, state_inner, state_inner]
    apply Finset.sum_congr rfl
    intro H hH
    by_cases h : SameFiber {i,j} G.val H.val
    · simp [restrictCell, h]
    · simp [z, localizedVector, restrictCell, h]

end Problem315.PairEquality

end

end OAI
