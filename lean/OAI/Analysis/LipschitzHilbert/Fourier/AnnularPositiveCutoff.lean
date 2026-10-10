import OAI.Analysis.LipschitzHilbert.Fourier.AnnularCutoffConstruction
import OAI.Analysis.LipschitzHilbert.Fourier.RescaledPartitionedSymbol

namespace OAI

/-! The positive half of the geometric low-pass difference is Schwartz
and is exactly covered by a fixed admissible enlarged cutoff. -/
noncomputable section
open MeasureTheory Function Set
namespace LipschitzHilbert.PacketRepresentation

def reassemblyDifferenceSchwartz : SchwartzMap ℝ ℂ :=
  dilatedSlopeWindow reassemblyLow (16/27) (by norm_num)-
    dilatedSlopeWindow reassemblyLow (8/9) (by norm_num)

@[simp] theorem reassemblyDifferenceSchwartz_apply (s : ℝ) :
    reassemblyDifferenceSchwartz s=reassemblyDifference s := rfl

def reassemblyPositive : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ reassemblyOuter reassemblyDifferenceSchwartz

@[simp] theorem reassemblyPositive_apply (s : ℝ) :
    reassemblyPositive s=reassemblyOuter s*reassemblyDifference s := by
  rw [reassemblyPositive,SchwartzMap.smulLeftCLM_apply_apply reassemblyOuter.hasTemperateGrowth,
    reassemblyDifferenceSchwartz_apply,smul_eq_mul]

theorem reassemblyPositive_active (s : ℝ) (hs : reassemblyPositive s≠0) :
    9/8≤s ∧ s≤117/64 := by
  have hp : reassemblyOuter s≠0 := by
    intro hz
    exact hs (by rw [reassemblyPositive_apply,hz,zero_mul])
  have hd : reassemblyDifference s≠0 := by
    intro hz
    exact hs (by rw [reassemblyPositive_apply,hz,mul_zero])
  have hpos : 0≤s := (reassemblyOuter_support s hp).1.trans' (by norm_num)
  have hlo : 9/8 < |s| := lt_of_not_ge (fun h => hd (reassemblyDifference_small s h))
  have hhi : |s|<117/64 := lt_of_not_ge (fun h => hd (reassemblyDifference_large s h))
  rw [abs_of_nonneg hpos] at hlo hhi
  exact ⟨hlo.le,hhi.le⟩

theorem reassemblyPositive_support (s : ℝ) (hs : reassemblyPositive s≠0) : 1≤s ∧ s≤2 := by
  have h := reassemblyPositive_active s hs
  constructor <;> linarith only [h.1,h.2]

theorem reassemblyPositive_enlarged (s : ℝ) :
    reassemblyOuter s*reassemblyPositive s=reassemblyPositive s := by
  by_cases hs : reassemblyPositive s=0
  · simp only [hs,mul_zero]
  · have h := reassemblyPositive_active s hs
    rw [reassemblyOuter_one s ⟨h.1,by linarith only [h.2]⟩,one_mul]

theorem reassemblyDifference_real (s : ℝ) : star (reassemblyDifference s)=reassemblyDifference s := by
  simp only [reassemblyDifference,reassemblyLow_apply,map_sub,Complex.star_def,Complex.conj_ofReal]

theorem reassemblyPositive_real (s : ℝ) : star (reassemblyPositive s)=reassemblyPositive s := by
  simp only [reassemblyPositive_apply,star_mul,reassemblyDifference_real,
    reassemblyOuter_apply,Complex.star_def,Complex.conj_ofReal]
  ring

theorem reassemblyDifference_even (s : ℝ) : reassemblyDifference (-s)=reassemblyDifference s := by
  simp only [reassemblyDifference,reassemblyLow_apply,mul_neg,reassemblyLowBump.neg]

end LipschitzHilbert.PacketRepresentation

end

end OAI
