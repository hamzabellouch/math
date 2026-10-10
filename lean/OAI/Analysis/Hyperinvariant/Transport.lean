import OAI.Analysis.Hyperinvariant.Specification

namespace OAI

namespace Hyperinvariant
open Filter
open scoped Topology
universe u v
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_conjugate_le (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖e.conjStarAlgEquiv T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖e (T (e.symm x))‖ ≤ ‖T‖ * ‖x‖
  rw [e.norm_map]
  simpa only [e.symm.norm_map] using T.le_opNorm (e.symm x)

theorem norm_conjugate (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖e.conjStarAlgEquiv T‖ = ‖T‖ := by
  apply le_antisymm (norm_conjugate_le e T)
  have he : e.symm.conjStarAlgEquiv (e.conjStarAlgEquiv T) = T := by
    ext x
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply]
  have h := norm_conjugate_le e.symm (e.conjStarAlgEquiv T)
  rwa [he] at h

/-- Hyperinvariance is transported through a genuine surjective complex-linear isometry. -/
theorem transitiveCommutant_conjugate (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H)
    (hT : TransitiveCommutant T) : TransitiveCommutant (e.conjStarAlgEquiv T) := by
  intro W hW hInv
  let U : Submodule ℂ H := W.comap e.toLinearMap
  have hU : IsClosed (U : Set H) := hW.preimage e.continuous
  have hUI : ∀ A : H →L[ℂ] H, A * T = T * A → ∀ x ∈ U, A x ∈ U := by
    intro A hA x hx
    change e (A x) ∈ W
    have hc : e.conjStarAlgEquiv A * e.conjStarAlgEquiv T =
        e.conjStarAlgEquiv T * e.conjStarAlgEquiv A := by
      simpa only [map_mul] using congrArg e.conjStarAlgEquiv hA
    have hm := hInv (e.conjStarAlgEquiv A) hc (e x) hx
    simpa using hm
  rcases hT U hU hUI with hz | ho
  · left
    apply le_antisymm _ bot_le
    intro y hy
    have hx : e.symm y ∈ U := by change e (e.symm y) ∈ W; simpa using hy
    rw [hz] at hx
    have hzero : e.symm y = 0 := hx
    have := congrArg e hzero
    simpa using this
  · right
    apply le_antisymm le_top
    intro y _
    have hx : e.symm y ∈ U := by rw [ho]; trivial
    change e (e.symm y) ∈ W at hx
    simpa using hx

/-- Nonzero and the exact norm-root limit are both preserved by unitary conjugation. -/
theorem mainClaim_transport (e : H ≃ₗᵢ[ℂ] K) (h : MainClaim (H := H)) :
    MainClaim (H := K) := by
  obtain ⟨T, hT0, hq, ht⟩ := h
  refine ⟨e.conjStarAlgEquiv T, ?_, ?_, transitiveCommutant_conjugate e T ht⟩
  · exact fun hzero => hT0 (e.conjStarAlgEquiv.injective (by simpa using hzero))
  · have he : (fun n : ℕ => ‖(e.conjStarAlgEquiv T) ^ n‖ ^ (1 / (n : ℝ))) =
        (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) := by
      funext n
      rw [← map_pow, norm_conjugate]
    rwa [he]

end Hyperinvariant

end OAI
