import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.TruncationIntegrability
import OAI.Analysis.RieszRectifiability.Nets.NativeCellMeanBounds

namespace OAI

/-!
# Decomposition of native truncations

Global upper growth makes hard-truncated kernels integrable against square-integrable
inputs, so truncation respects addition. On cells of finite mass, the same decomposition
passes to means of scalar components of the resulting vector-valued transforms.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

theorem truncated_add_of_globalGrowth {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (ε : ℝ) (hε : 0 < ε) (f g : Ambient d → ℝ)
    (hf : MemLp f 2 μ) (hh : MemLp g 2 μ) (x : Ambient d) :
    truncated n μ ε (fun y => f y + g y) x =
      truncated n μ ε f x + truncated n μ ε g x := by
  unfold truncated
  simp only [add_smul]
  exact integral_add (truncation_integrable_of_globalGrowth n hn G μ hg f hf x ε hε)
    (truncation_integrable_of_globalGrowth n hn G μ hg g hh x ε hε)

theorem three_part_truncated_cellMean {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (ε : ℝ) (hε : 0 < ε) (f g h : Ambient d → ℝ)
    (hf : MemLp f 2 μ) (hhg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (huf : MemLp (truncated n μ ε f) 2 μ) (hug : MemLp (truncated n μ ε g) 2 μ)
    (huh : MemLp (truncated n μ ε h) 2 μ)
    (A : Set (Ambient d)) (hfin : μ A < ∞) (e : Ambient d) :
    cellMean (μ.restrict A) (fun x => inner ℝ e
      (truncated n μ ε (fun y => f y + g y + h y) x)) =
    cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε f x)) +
    cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε g x)) +
    cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε h x)) := by
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  have hif := ((memLp_inner_const_of_vector μ _ huf e).restrict A).integrable (by norm_num)
  have hig := ((memLp_inner_const_of_vector μ _ hug e).restrict A).integrable (by norm_num)
  have hih := ((memLp_inner_const_of_vector μ _ huh e).restrict A).integrable (by norm_num)
  have heq : (fun x => inner ℝ e (truncated n μ ε (fun y => f y + g y + h y) x)) =
      (fun x => inner ℝ e (truncated n μ ε f x) + inner ℝ e (truncated n μ ε g x) +
        inner ℝ e (truncated n μ ε h x)) := by
    funext x
    rw [truncated_add_of_globalGrowth n hn G μ hg ε hε (fun y => f y + g y) h (hf.add hhg) hh x,
      truncated_add_of_globalGrowth n hn G μ hg ε hε f g hf hhg x,
      inner_add_right, inner_add_right]
  rw [heq]
  rw [cellMean_add (μ.restrict A)
    (fun x => inner ℝ e (truncated n μ ε f x) + inner ℝ e (truncated n μ ε g x))
    (fun x => inner ℝ e (truncated n μ ε h x)) (hif.add hig) hih,
    cellMean_add (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε f x))
      (fun x => inner ℝ e (truncated n μ ε g x)) hif hig]

end

end RieszRectifiability

end OAI
