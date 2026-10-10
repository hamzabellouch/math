import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

namespace OAI

noncomputable section

namespace Invariant233.PositiveSelfAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem one_add_range_orthogonal_eq_bot
    (H : E →ₗ.[ℂ] E) (hH : IsSelfAdjoint H)
    (hpos : ∀ x : H.domain, 0 ≤ (inner ℂ (x : E) (H x)).re) :
    (LinearMap.range (H.domain.subtype + H.toFun))ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro y hy
  have hzero (x : H.domain) : inner ℂ y ((x : E) + H x) = 0 := by
    exact Submodule.inner_left_of_mem_orthogonal
      (show (x : E) + H x ∈ LinearMap.range (H.domain.subtype + H.toFun) from
        ⟨x, rfl⟩) hy
  have hinner (x : H.domain) : inner ℂ (-y) (x : E) = inner ℂ y (H x) := by
    have hx := hzero x
    rw [inner_add_right] at hx
    rw [inner_neg_left]
    exact neg_eq_iff_add_eq_zero.mpr hx
  have hadj : H.adjoint = H := LinearPMap.isSelfAdjoint_def.mp hH
  have hyadj : y ∈ H.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨-y, hinner⟩
  have hyD : y ∈ H.domain := by simpa only [hadj] using hyadj
  have hHy : H ⟨y, hyD⟩ = -y := by
    have heq := LinearPMap.adjoint_apply_eq hH.dense_domain
      (⟨y, hyadj⟩ : H.adjoint.domain) hinner
    exact ((le_of_eq hadj).2 (show (⟨y, hyadj⟩ : H.adjoint.domain).val =
      (⟨y, hyD⟩ : H.domain).val from rfl)).symm.trans heq
  have hp := hpos ⟨y, hyD⟩
  change 0 ≤ (inner ℂ y (H ⟨y, hyD⟩)).re at hp
  rw [hHy, inner_neg_right, Complex.neg_re] at hp
  have hnorm : (inner ℂ y y).re = ‖y‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) y
  rw [hnorm] at hp
  change y = 0
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg y]

theorem denseRange_one_add
    (H : E →ₗ.[ℂ] E) (hH : IsSelfAdjoint H)
    (hpos : ∀ x : H.domain, 0 ≤ (inner ℂ (x : E) (H x)).re) :
    DenseRange (fun x : H.domain => (x : E) + H x) := by
  change Dense (LinearMap.range (H.domain.subtype + H.toFun) : Set E)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure]
  exact one_add_range_orthogonal_eq_bot H hH hpos

end Invariant233.PositiveSelfAdjoint

end

end OAI
