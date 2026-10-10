import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ADTruncations

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem truncated_congr_ae {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (ε : ℝ) {f g : Ambient d → ℝ} (hfg : f =ᵐ[μ] g) :
    truncated n μ ε f = truncated n μ ε g := by
  funext x
  unfold truncated
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hfg] with y hy
  rw [hy]

theorem truncated_add {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (hAD : ADRegular n μ)
    (ε : ℝ) (hε : 0 < ε) (f g : Ambient d → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    truncated n μ ε (f + g) = truncated n μ ε f + truncated n μ ε g := by
  funext x
  unfold truncated
  simp only [Pi.add_apply, add_smul]
  exact integral_add (truncation_integrable_of_ADRegular n hn μ hAD f hf x ε hε)
    (truncation_integrable_of_ADRegular n hn μ hAD g hg x ε hε)

theorem truncated_smul {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (ε c : ℝ) (f : Ambient d → ℝ) :
    truncated n μ ε (c • f) = c • truncated n μ ε f := by
  funext x
  unfold truncated
  simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul]
  exact integral_smul c _

def truncationLp {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (ε : ℝ)
    (hB : ∀ f : Ambient d → ℝ, MemLp f 2 μ → MemLp (truncated n μ ε f) 2 μ)
    (f : Lp ℝ 2 μ) : Lp (Ambient d) 2 μ :=
  (hB f (Lp.memLp f)).toLp (truncated n μ ε f)

theorem truncationLp_coe {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (ε : ℝ)
    (hB : ∀ f : Ambient d → ℝ, MemLp f 2 μ → MemLp (truncated n μ ε f) 2 μ)
    (f : Lp ℝ 2 μ) :
    truncationLp n μ ε hB f =ᵐ[μ] truncated n μ ε f :=
  MemLp.coeFn_toLp _

theorem truncationLp_add {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (hAD : ADRegular n μ)
    (ε : ℝ) (hε : 0 < ε)
    (hB : ∀ f : Ambient d → ℝ, MemLp f 2 μ → MemLp (truncated n μ ε f) 2 μ)
    (f g : Lp ℝ 2 μ) :
    truncationLp n μ ε hB (f + g) = truncationLp n μ ε hB f + truncationLp n μ ε hB g := by
  have heq : truncated n μ ε (⇑(f + g)) =
      truncated n μ ε f + truncated n μ ε g :=
    (truncated_congr_ae n μ ε (Lp.coeFn_add f g)).trans
      (truncated_add n hn μ hAD ε hε f g (Lp.memLp f) (Lp.memLp g))
  exact (MemLp.toLp_congr (hB _ (Lp.memLp (f + g)))
    ((hB _ (Lp.memLp f)).add (hB _ (Lp.memLp g)))
    (Filter.Eventually.of_forall fun x => congrFun heq x)).trans
      (MemLp.toLp_add _ _)

theorem truncationLp_smul {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (ε : ℝ)
    (hB : ∀ f : Ambient d → ℝ, MemLp f 2 μ → MemLp (truncated n μ ε f) 2 μ)
    (c : ℝ) (f : Lp ℝ 2 μ) :
    truncationLp n μ ε hB (c • f) = c • truncationLp n μ ε hB f := by
  have heq : truncated n μ ε (⇑(c • f)) = c • truncated n μ ε f :=
    (truncated_congr_ae n μ ε (Lp.coeFn_smul c f)).trans (truncated_smul n μ ε c f)
  exact (MemLp.toLp_congr (hB _ (Lp.memLp (c • f)))
    ((hB _ (Lp.memLp f)).const_smul c)
    (Filter.Eventually.of_forall fun x => congrFun heq x)).trans
      (MemLp.toLp_const_smul _ _)

def truncationLinearMap {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (hAD : ADRegular n μ)
    (ε : ℝ) (hε : 0 < ε)
    (hB : ∀ f : Ambient d → ℝ, MemLp f 2 μ → MemLp (truncated n μ ε f) 2 μ) :
    Lp ℝ 2 μ →ₗ[ℝ] Lp (Ambient d) 2 μ where
  toFun := truncationLp n μ ε hB
  map_add' := truncationLp_add n hn μ hAD ε hε hB
  map_smul' := truncationLp_smul n μ ε hB

end

end RieszRectifiability

end OAI
