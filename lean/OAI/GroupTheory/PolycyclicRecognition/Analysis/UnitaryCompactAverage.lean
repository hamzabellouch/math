import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteUnitaryAverage

namespace OAI

/-! # Uniformly small unitary averages on a compact set of vectors -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {G E : Type*} [Group G] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_unitaryAverage_small_compact
    (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (hfixed : ∀ x : E, (∀ g, ρ g x = x) → x = 0)
    (K : Set E) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : FiniteOrbitAverage G, ∀ x ∈ K, ‖A.onVector ρ x‖ < ε := by
  classical
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨s, _, hs, hcover⟩ := hK.elim_finite_subcover_image
    (b := K) (c := fun y => ball y (ε / 2)) (fun _ _ => isOpen_ball)
    (fun x hx => mem_iUnion.2 ⟨x, mem_iUnion.2 ⟨hx, mem_ball_self hhalf⟩⟩)
  let := hs.fintype
  obtain ⟨A, hA⟩ := exists_unitaryAverage_small_finite ρ hfixed
    (fun y : s => (y : E)) hhalf
  refine ⟨A, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  have hd : ‖x - y‖ < ε / 2 := by simpa only [mem_ball, dist_eq_norm] using hxy
  calc
    ‖A.onVector ρ x‖ ≤ ‖A.onVector ρ x - A.onVector ρ y‖ + ‖A.onVector ρ y‖ :=
      norm_le_norm_sub_add _ _
    _ = ‖A.onVector ρ (x - y)‖ + ‖A.onVector ρ y‖ := by rw [A.onVector_sub]
    _ ≤ ‖x - y‖ + ‖A.onVector ρ y‖ := add_le_add (A.norm_onVector_le ρ _) le_rfl
    _ < ε := by have hv := hA ⟨y, hy⟩; linarith

end PolycyclicRecognition

end

end OAI
