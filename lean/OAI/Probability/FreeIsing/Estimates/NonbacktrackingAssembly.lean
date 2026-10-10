import OAI.Probability.FreeIsing.Estimates.NonbacktrackingComplement
import OAI.Probability.FreeIsing.Spectral.OrthogonalBlocks

namespace OAI

noncomputable section

open scoped InnerProduct

namespace Problem367.NonbacktrackingComplement

variable {𝕜 E V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

theorem edgeOperator_apply_tail
    (c r : ℝ) (hcr : c - r = 1)
    (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V)
    (hFF : ∀ x, (F†) (F x) = x) (hJF : ∀ x, J (F x) = H x) (x : E) :
    edgeOperator c r F H J (F x) = H x := by
  change (c : 𝕜) • H ((F†) (F x)) - (r : 𝕜) • J (F x) = H x
  rw [hFF, hJF, ← sub_smul]
  have hc : (c : 𝕜) - (r : 𝕜) = 1 := by
    exact_mod_cast hcr
  rw [hc, one_smul]

theorem edgeOperator_apply_head
    (c r : ℝ) (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    (hFH : ∀ x, (F†) (H x) = A x) (hJH : ∀ x, J (H x) = F x) (x : E) :
    edgeOperator c r F H J (H x) = (c : 𝕜) • H (A x) - (r : 𝕜) • F x := by
  simp [edgeOperator, hFH, hJH]

theorem edgeOperator_apply_liftSum
    (c r : ℝ) (hcr : c - r = 1)
    (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    (hFF : ∀ x, (F†) (F x) = x) (hFH : ∀ x, (F†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x) (x y : E) :
    edgeOperator c r F H J (F x + H y) =
      F (-(r : 𝕜) • y) + H (x + (c : 𝕜) • A y) := by
  rw [map_add, edgeOperator_apply_tail c r hcr F H J hFF hJF,
    edgeOperator_apply_head c r F H J A hFH hJH]
  simp only [map_add, map_smul, neg_smul, map_neg]
  abel

theorem edgeOperator_mem_liftRange
    (c r : ℝ) (hcr : c - r = 1)
    (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    (hFF : ∀ x, (F†) (F x) = x) (hFH : ∀ x, (F†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    {y : V} (hy : y ∈ F.range ⊔ H.range) :
    edgeOperator c r F H J y ∈ F.range ⊔ H.range := by
  rcases Submodule.mem_sup.mp hy with ⟨u, ⟨x, rfl⟩, v, ⟨z, rfl⟩, rfl⟩
  change edgeOperator c r F H J (F x + H z) ∈ F.range ⊔ H.range
  rw [edgeOperator_apply_liftSum c r hcr F H J A hFF hFH hJF hJH]
  exact Submodule.mem_sup.mpr
    ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩

theorem norm_edgeOperator_pow_le_max
    (c r : ℝ) (hr : 0 ≤ r) (hcr : c - r = 1)
    (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    [(F.range ⊔ H.range).HasOrthogonalProjection]
    (hFF : ∀ x, (F†) (F x) = x) (hFH : ∀ x, (F†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ F.range ⊔ H.range,
      ‖(edgeOperator c r F H J ^ n) x‖ ≤ C * ‖x‖) :
    ‖edgeOperator c r F H J ^ n‖ ≤ max C (r ^ n) := by
  refine OrthogonalBlocks.norm_pow_le_of_orthogonal_blocks
    (edgeOperator c r F H J) (F.range ⊔ H.range)
    (fun x hx => edgeOperator_mem_liftRange c r hcr F H J A hFF hFH hJF hJH hx)
    ?_ n hC (pow_nonneg hr n) hbound ?_
  · intro x hx
    rw [← liftComplement_eq_orthogonal] at hx ⊢
    exact edgeOperator_mem_liftComplement c r F H J hJF hJH hx
  · intro x hx
    rw [← liftComplement_eq_orthogonal] at hx
    exact (norm_edgeOperator_pow c r hr F H J hJF hJH hx n).le

end Problem367.NonbacktrackingComplement

end

end OAI
