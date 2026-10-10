import OAI.Probability.InvariantIsing.Pressure.RandomSpectralBound
import Mathlib.MeasureTheory.Order.Lattice

namespace OAI

/-! Measurability of the finite-dimensional spectral norm bound. -/
noncomputable section
open MeasureTheory
namespace InvariantIsing

lemma spectralRadius_eq_sup_abs {n : ℕ} (eig : Fin (n+1) → ℝ) :
    spectralRadius eig=Finset.univ.sup' Finset.univ_nonempty (fun i => |eig i|) := by
  apply le_antisymm
  · apply (spectralRadius_le_iff _ _).mpr
    intro i
    exact Finset.le_sup' (fun i => |eig i|) (Finset.mem_univ i)
  · exact Finset.sup'_le Finset.univ_nonempty _ fun i _ => abs_le_spectralRadius eig i

lemma measurable_spectralRadius {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (eig : Ω → Fin (n+1) → ℝ) (heig : Measurable eig) :
    Measurable (fun ω => spectralRadius (eig ω)) := by
  have hh := Finset.measurable_sup' (s := (Finset.univ : Finset (Fin (n+1))))
    Finset.univ_nonempty (fun i _ => ((measurable_pi_apply i).comp heig).abs)
  convert hh using 1
  funext ω
  rw [spectralRadius_eq_sup_abs,Finset.sup'_apply]
  rfl

end InvariantIsing

end

end OAI
