import OAI.Analysis.MassAction.FixedMinimum
import OAI.Analysis.MassAction.AffineTrajectory

namespace OAI

noncomputable section

open Set

namespace Problem326.Affine

/-- The comparison-based activity convention agrees with attaining the finite
minimum, including every tied branch. -/
theorem active_iff_value_eq_inf {d : ℕ} {Λ : Finset (Label d)}
    (hne : Λ.Nonempty) {L : Label d} {h : ℝ} {z : Fin d → ℝ} :
    Active Λ L h z ↔
      L ∈ Λ ∧ L.value h z = Λ.inf' hne (fun J => J.value h z) := by
  constructor
  · intro hL
    exact ⟨hL.1, le_antisymm ((Finset.le_inf'_iff hne (fun J => J.value h z)).2 hL.2)
      (Finset.inf'_le _ hL.1)⟩
  · rintro ⟨hL, heq⟩
    refine ⟨hL, fun J hJ => ?_⟩
    rw [heq]
    exact Finset.inf'_le _ hJ

/-- Canonical affine labels directly supply the finite-interval trapping
principle. Only active slopes inside the closed region need point inward. -/
theorem trapped_of_active_inward
    {d : ℕ} (Λ : Finset (Label d)) (hne : Λ.Nonempty) (h : ℝ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (B : Set (Fin d → ℝ))
    {x : ℝ → (Fin d → ℝ)} {T M : ℝ}
    (hT : 0 ≤ T) (hclosed : IsClosed B)
    (hx : ContinuousOn x (Icc 0 T))
    (hxd : ∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t)) t)
    (hx0 : x 0 ∈ interior B)
    (hinward : ∀ z ∈ B, ∀ L, Active Λ L h z →
      0 ≤ dot L.slope (f z))
    (hceiling : ∀ z ∈ B, Λ.inf' hne (fun L => L.value h z) ≤ M)
    (hstart : Λ.inf' hne (fun L => L.value h (x 0)) = M)
    (hboundary : ∀ z ∈ frontier B,
      Λ.inf' hne (fun L => L.value h z) ≠ M) :
    MapsTo x (Icc 0 T) (interior B) ∧
      ∀ t ∈ Icc 0 T, Λ.inf' hne (fun L => L.value h (x t)) = M := by
  apply Problem326.affineMinimum_trapped Λ hne Label.slope (fun L => L.offset h)
    f B hT hclosed hx hxd hx0
  · intro z hz L hL hactive
    apply hinward z hz L
    exact (active_iff_value_eq_inf hne).2 ⟨hL, hactive⟩
  · exact hceiling
  · exact hstart
  · exact hboundary

end Problem326.Affine

end

end OAI
