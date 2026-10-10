import OAI.Analysis.KadisonKastler.HilbertMatrix
import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

/-! Uniform rectangular matrix bounds are closed under entrywise weak limits. -/

namespace KadisonKastler

noncomputable section

open Filter Generator
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance weakMatrixOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance weakMatrixStarOrder : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

theorem weak_operator_ultralimit_norm_le {ι : Type*} (ω : Ultrafilter ι)
    (F : ι → H →L[ℂ] H) (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ i, ‖F i‖ ≤ c)
    (ht : ∀ ξ η, Tendsto (fun i => inner ℂ η (F i ξ)) (ω : Filter ι)
      (𝓝 (inner ℂ η (T ξ)))) : ‖T‖ ≤ c := by
  obtain ⟨S, hS, hs⟩ := Tracial.exists_weak_operator_ultralimit ω F c hc hF
  have he : S = T := by
    ext ξ
    apply ext_inner_left ℂ
    intro η
    exact tendsto_nhds_unique (hs ξ η) (ht ξ η)
  rwa [he] at hS

theorem square_matrix_ultralimit_norm_le {ι n : Type*} [Fintype n] [DecidableEq n]
    (ω : Ultrafilter ι) (F : ι → CStarMatrix n n (H →L[ℂ] H))
    (T : CStarMatrix n n (H →L[ℂ] H)) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ i, ‖F i‖ ≤ c)
    (ht : ∀ a b ξ η, Tendsto (fun i => inner ℂ η (F i a b ξ)) (ω : Filter ι)
      (𝓝 (inner ℂ η (T a b ξ)))) : ‖T‖ ≤ c := by
  rw [← norm_hilbertMatrix]
  apply weak_operator_ultralimit_norm_le ω (fun i => hilbertMatrix (F i)) _ hc
  · intro i
    rw [norm_hilbertMatrix]
    exact hF i
  · intro ξ η
    simp only [PiLp.inner_apply, hilbertMatrix_apply, inner_sum]
    exact tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
      ht a b (ξ b) (η a)

theorem rectangular_matrix_ultralimit_norm_le {ι m n : Type*} [Fintype m] [Fintype n]
    (ω : Ultrafilter ι) (F : ι → CStarMatrix m n (H →L[ℂ] H))
    (T : CStarMatrix m n (H →L[ℂ] H)) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ i, ‖F i‖ ≤ c)
    (ht : ∀ a b ξ η, Tendsto (fun i => inner ℂ η (F i a b ξ)) (ω : Filter ι)
      (𝓝 (inner ℂ η (T a b ξ)))) : ‖T‖ ≤ c := by
  classical
  rw [← norm_rectangularCorner]
  apply square_matrix_ultralimit_norm_le ω (fun i => rectangularCorner (F i)) _ hc
  · intro i
    rw [norm_rectangularCorner]
    exact hF i
  · intro a b ξ η
    rcases a with a | a <;> rcases b with b | b
    · simpa only [rectangularCorner] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => inner ℂ η ((0 : H →L[ℂ] H) ξ))
          (ω : Filter ι) (𝓝 (inner ℂ η ((0 : H →L[ℂ] H) ξ))))
    · exact ht a b ξ η
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds

end

end KadisonKastler

end OAI
