import OAI.Analysis.LipschitzHilbert.Estimates.DyadicWeakL1
import OAI.Analysis.LipschitzHilbert.Trees.SourceAllDyadicMaximal

namespace OAI

/-! Weak L1 control at all integer scales, using the extended supremum
so that the pointwise domination has no exceptional-set convention. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.DyadicLineGrid

def allDyadicSup (q : ℤ) (f : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ k : ℤ, ENNReal.ofReal |cellMean q k f x|

theorem allDyadicSup_measurable (q : ℤ) (f : ℝ → ℝ) : Measurable (allDyadicSup q f) :=
  Measurable.iSup (fun k => ((cellMean_measurable q k f).norm.ennreal_ofReal))

theorem cellMean_le_allDyadicSup (q k : ℤ) (f : ℝ → ℝ) (x : ℝ) :
    ENNReal.ofReal |cellMean q k f x| ≤ allDyadicSup q f x :=
  le_iSup (fun k : ℤ => ENNReal.ofReal |cellMean q k f x|) k

theorem allDyadicSup_weak_L1 (q : ℤ) {f : ℝ → ℝ} (hf : Integrable f volume)
    (t : ℝ) (ht : 0<t) :
    volume {x | ENNReal.ofReal t<allDyadicSup q f x} ≤ ENNReal.ofReal (t⁻¹*(∫ x, |f x|)) := by
  let E := fun N : ℕ => {x | t<dyadicMaximal q (N:ℤ) (2*N) f x}
  have hmono : Monotone E := by
    intro i j hij x hx
    exact hx.trans_le (dyadicWindow_mono q f hij x)
  have hsub : {x | ENNReal.ofReal t<allDyadicSup q f x}⊆⋃ N, E N := by
    intro x hx
    change ENNReal.ofReal t < ⨆ k : ℤ, ENNReal.ofReal |cellMean q k f x| at hx
    obtain ⟨k,hk⟩ := (lt_iSup_iff).mp hx
    have hk' : t < |cellMean q k f x| := by
      by_contra hn
      exact not_lt_of_ge (ENNReal.ofReal_le_ofReal (le_of_not_gt hn)) hk
    exact mem_iUnion.mpr ⟨k.natAbs,hk'.trans_le (cellMean_le_window q k f x)⟩
  calc
    _  ≤  volume (⋃ N, E N) := measure_mono hsub
    _ = ⨆ N, volume (E N) := hmono.measure_iUnion
    _  ≤  _ := by
      apply iSup_le
      intro N
      exact (measure_mono (show E N⊆{x | t ≤ dyadicMaximal q (N:ℤ) (2*N) f x} from
        fun x hx => (show t < dyadicMaximal q (N:ℤ) (2*N) f x from hx).le)).trans (dyadicMaximal_weak_L1 q N hf (2*N) t ht)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
