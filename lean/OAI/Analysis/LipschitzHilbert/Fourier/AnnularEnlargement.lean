import OAI.Analysis.LipschitzHilbert.Fourier.AnnularPartitionIdentities

namespace OAI

/-! A fixed symmetric enlarged annular cutoff is one on every nonzero
piece of the concrete annular resolution. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketRepresentation

def reassemblyEnlarged : SchwartzMap ℝ ℂ :=
  reassemblyOuter+conjugateReflectedCutoff reassemblyOuter

@[simp] theorem reassemblyEnlarged_apply (x : ℝ) :
    reassemblyEnlarged x=reassemblyOuter x+reassemblyOuter (-x) := by
  simp only [reassemblyEnlarged,add_apply,conjugateReflectedCutoff_apply,
    reassemblyOuter_apply,Complex.conj_ofReal]

theorem reassemblyEnlarged_absorb (x : ℝ) :
    reassemblyEnlarged x*reassemblyDifference x=reassemblyDifference x := by
  have h := reassemblyPositive_halfsum x
  rw [reassemblyPositive_apply,reassemblyPositive_apply,reassemblyDifference_even] at h
  rw [reassemblyEnlarged_apply,add_mul]
  exact h

theorem reassemblyEnlarged_support (x : ℝ) (hx : reassemblyEnlarged x≠0) :
    1≤|x| ∧ |x|≤2 := by
  by_cases hp : reassemblyOuter x=0
  · have hn : reassemblyOuter (-x)≠0 := by
      intro hz
      exact hx (by rw [reassemblyEnlarged_apply,hp,hz,add_zero])
    have h := reassemblyOuter_support (-x) hn
    have hxneg : x≤0 := by linarith [h.1]
    rw [abs_of_nonpos hxneg]
    exact h
  · have h := reassemblyOuter_support x hp
    rw [abs_of_nonneg (show 0≤x by linarith [h.1])]
    exact h

theorem reassemblyEnlarged_tsupport :
    tsupport reassemblyEnlarged ⊆ {x : ℝ | 1≤|x| ∧ |x|≤2} := by
  exact closure_minimal (fun x hx => reassemblyEnlarged_support x hx)
    ((isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const))

theorem reassemblyEnlarged_away_zero :
    tsupport reassemblyEnlarged ⊆ {x : ℝ | 1/2≤|x|} := by
  intro x hx
  have h := (reassemblyEnlarged_tsupport hx).1
  change (1/2:ℝ)≤|x|
  linarith

theorem reassemblyEnlarged_bounded_support :
    tsupport reassemblyEnlarged ⊆ Icc (-2:ℝ) 2 := by
  intro x hx
  exact abs_le.mp (reassemblyEnlarged_tsupport hx).2

end LipschitzHilbert.PacketRepresentation

end

end OAI
