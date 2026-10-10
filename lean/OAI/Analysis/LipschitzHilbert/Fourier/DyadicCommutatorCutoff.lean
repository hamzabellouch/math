import OAI.Analysis.LipschitzHilbert.Fourier.DyadicSmoothCutoff

namespace OAI

/-! A fixed enlarged annulus for the low/high part of the commutator.
Its support fits the already proved localized Mihlin kernel estimates. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketRepresentation

def dyadicCommutatorCutoff : SchwartzMap ℝ ℂ :=
  dilatedSlopeWindow reassemblyLow (2/3) (by norm_num)-
    dilatedSlopeWindow reassemblyLow 2 (by norm_num)

@[simp] theorem dyadicCommutatorCutoff_apply (x : ℝ) :
    dyadicCommutatorCutoff x=reassemblyLow ((2/3)*x)-reassemblyLow (2*x) := by
  simp only [dyadicCommutatorCutoff,sub_apply,dilatedSlopeWindow_apply]

theorem dyadicCommutatorCutoff_one (x : ℝ) (hx : 13/24≤|x| ∧ |x|≤3/2) :
    dyadicCommutatorCutoff x=1 := by
  have hsmall : |(2/3)*x|≤1 := by rw [abs_mul]; norm_num; linarith [hx.2]
  have hlarge : 13/12≤|2*x| := by rw [abs_mul]; norm_num; linarith [hx.1]
  rw [dyadicCommutatorCutoff_apply,reassemblyLow_one _ hsmall,reassemblyLow_zero _ hlarge,sub_zero]

theorem dyadicCommutatorCutoff_small (x : ℝ) (hx : |x|≤1/2) :
    dyadicCommutatorCutoff x=0 := by
  have h1 : |(2/3)*x|≤1 := by rw [abs_mul]; norm_num; linarith
  have h2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
  rw [dyadicCommutatorCutoff_apply,reassemblyLow_one _ h1,reassemblyLow_one _ h2,sub_self]

theorem dyadicCommutatorCutoff_large (x : ℝ) (hx : 13/8≤|x|) :
    dyadicCommutatorCutoff x=0 := by
  have h1 : 13/12≤|(2/3)*x| := by rw [abs_mul]; norm_num; linarith
  have h2 : 13/12≤|2*x| := by rw [abs_mul]; norm_num; linarith
  rw [dyadicCommutatorCutoff_apply,reassemblyLow_zero _ h1,reassemblyLow_zero _ h2,sub_self]

theorem dyadicCommutatorCutoff_tsupport :
    tsupport dyadicCommutatorCutoff ⊆ {x : ℝ | 1/2≤|x| ∧ |x|≤13/8} := by
  apply closure_minimal _ ((isClosed_le continuous_const continuous_abs).inter
    (isClosed_le continuous_abs continuous_const))
  intro x hx
  exact ⟨(lt_of_not_ge (fun h => hx (dyadicCommutatorCutoff_small x h))).le,
    (lt_of_not_ge (fun h => hx (dyadicCommutatorCutoff_large x h))).le⟩

theorem dyadicCommutatorCutoff_away_zero :
    tsupport dyadicCommutatorCutoff ⊆ {x : ℝ | 1/2≤|x|} :=
  fun _ hx => (dyadicCommutatorCutoff_tsupport hx).1

theorem dyadicCommutatorCutoff_bounded_support :
    tsupport dyadicCommutatorCutoff ⊆ Icc (-2:ℝ) 2 := by
  intro x hx
  have h := (dyadicCommutatorCutoff_tsupport hx).2
  exact abs_le.mp (by linarith : |x|≤2)

end LipschitzHilbert.PacketRepresentation

end

end OAI
