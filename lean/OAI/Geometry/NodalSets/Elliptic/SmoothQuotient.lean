import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

namespace OAI

namespace Yau
noncomputable section
open Function Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem quotient_tsupport_subset (R D : E → ℝ) :
    tsupport (fun x ↦ R x / D x) ⊆ tsupport R := by
  apply closure_mono
  intro x hx
  simp only [mem_support] at *
  intro h
  exact hx (by simp [h])

theorem smooth_quotient_on_residual_support {R D : E → ℝ} {n : ℕ∞ω}
    (hR : ContDiff ℝ n R) (hD : ContDiff ℝ n D)
    (hn : ∀ x ∈ tsupport R, D x ≠ 0) :
    ContDiff ℝ n (fun x ↦ R x / D x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport R
  · exact hR.contDiffAt.div hD.contDiffAt (hn x hx)
  · have he : R =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

theorem smooth_quotient_from_region {R D : E → ℝ} {n : ℕ∞ω} {Ω : Set E}
    (hR : ContDiff ℝ n R) (hD : ContDiff ℝ n D)
    (hs : tsupport R ⊆ Ω) (hn : ∀ x ∈ Ω, D x ≠ 0) :
    ContDiff ℝ n (fun x ↦ R x / D x) :=
  smooth_quotient_on_residual_support hR hD (fun x hx ↦ hn x (hs hx))

omit [NormedSpace ℝ E] in
theorem quotient_compact_support {R D : E → ℝ} (hR : HasCompactSupport R) :
    HasCompactSupport (fun x ↦ R x / D x) := by
  exact hR.of_isClosed_subset isClosed_closure (quotient_tsupport_subset R D)

end
end Yau

end OAI
