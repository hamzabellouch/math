import Mathlib
import OAI.Analysis.FreeWords.PatchingCornerBounds
import OAI.Analysis.FreeWords.PatchingTermTrace
import OAI.Analysis.FreeWords.PatchingTerms

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKMatrixQuantization

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

theorem patching_term_bound {W : Set (PatchingWord (ConcreteAlgebra M))}
    (v w : PartialUnitary (ConcreteAlgebra M)) (t : PatchingTerms W)
    {a β : ℝ} (ha : 0≤a) (hβ : 0≤β) (c : ℂ)
    (hc : ‖c‖≤β)
    (hnorm : ∀ z∈t.1.val.raw, ‖z.1‖≤1) (hright : ‖t.1.val.right‖≤1)
    (hcomp : (traceNorm τ (w.support*t.split.gap v.power*w.support-c • w.support))^2≤a*(τ.map w.support).re)
    (hweak : ‖τ.map (w.power t.split.exponent*t.split.coefficient v.power t.1.val.right)‖≤a*(τ.map w.support).re) :
    ‖τ.map (Colored.value v.power w.power t.2.val*t.1.val.right)‖≤
      (β+Real.sqrt a+a)*(τ.map w.support).re := by
  have htq : 0≤(τ.map w.support).re := by
    rw [← traceNorm_projection_sq τ w.projection]
    exact sq_nonneg _
  have hall : ∀ z∈t.2.val, ‖z.1.1‖≤1 := by
    intro z hz
    apply hnorm z.1
    rw [← Colored.erase_of_mem_changes t.2.property]
    exact List.mem_map_of_mem hz
  cases he : t.split with
  | single p z s h =>
    rw [he] at hweak
    rw [h,trace_colored_single]
    have hh : ‖τ.map (w.power z.2*(PatchingWord.tailValue v.power s*t.1.val.right*
        PatchingWord.tailValue v.power p*z.1))‖≤a*(τ.map w.support).re := hweak
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg a]) htq)
  | multiple p z g y r h =>
    rw [he] at hcomp
    rw [h,trace_colored_multiple]
    have hrest := norm_colored_multiple_rest v w p g z y r t.1.val.right (h ▸ hall) hright
    have hh := gap_trace_small τ w z.2 y.2 (PatchingWord.tailValue v.power g*y.1)
      (Colored.value v.power w.power r*t.1.val.right*PatchingWord.tailValue v.power p*z.1)
      c ha hc hrest hcomp
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) htq)

end

end KKLocalPatching
end

end OAI
