import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.ConvexIsometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_fixed (K : Set H) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconv : Convex ℝ K) :
    ∃ z∈K, ∀ U : H →ₗᵢ[ℂ] H, (∀ x∈K, U x∈K) → U z=z := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨z,hz,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv (0:H)
  refine ⟨z,hz,?_⟩
  intro U hUK
  have huz := hUK z hz
  have hmin' : ‖(0:H)-U z‖=⨅ w : K, ‖(0:H)-(w:H)‖ := by
    simpa only [zero_sub,norm_neg,U.norm_map] using hmin
  have ha := (norm_eq_iInf_iff_real_inner_le_zero hconv hz).mp hmin (U z) huz
  have hb := (norm_eq_iInf_iff_real_inner_le_zero hconv huz).mp hmin' z hz
  have hc : ‖U z-z‖^2=‖U z‖^2-2*inner ℝ (U z) z+‖z‖^2 := norm_sub_sq_real _ _
  simp only [zero_sub,inner_neg_left,inner_sub_right,real_inner_self_eq_norm_sq] at ha hb
  have he : inner ℝ z (U z)=inner ℝ (U z) z := real_inner_comm _ _
  rw [he] at ha
  have hd : ‖U z-z‖=0 := by nlinarith [norm_nonneg (U z-z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hd)

omit [CompleteSpace H] in
lemma maps_closedConvexHull (U : H →ₗᵢ[ℂ] H) (S : Set H)
    (hU : ∀ x∈S, U x∈S) :
    ∀ x∈closedConvexHull ℝ S, U x∈closedConvexHull ℝ S := by
  have hconv : Convex ℝ (U ⁻¹' closedConvexHull ℝ S) :=
    convex_closedConvexHull.linear_preimage (U.toLinearMap.restrictScalars ℝ)
  have hcl : IsClosed (U ⁻¹' closedConvexHull ℝ S) :=
    isClosed_closedConvexHull.preimage U.continuous
  exact closedConvexHull_min (fun x hx => subset_closedConvexHull (hU x hx)) hconv hcl

end Kadison.ConvexIsometry

end

end
end

end OAI
