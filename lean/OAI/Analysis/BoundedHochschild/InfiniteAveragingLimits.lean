import OAI.Analysis.BoundedHochschild.NormalInfiniteAverages
import OAI.Analysis.BoundedHochschild.RightAveragingOrbit

namespace OAI

/-! Infinite normalized right averages are actual algebra-valued maps in the
original finite-averaging orbit closure, with the original factorization bound. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {I K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma normal_factorization_value_norm_le (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L W : NormalGNS e →L[ℂ] K) (x a : M)
    (hx : normalGNSRepresentation e x = L.adjoint.comp ((π a).comp W)) :
    ‖x‖ ≤ ‖L‖ * ‖a‖ * ‖W‖ := by
  calc
    ‖x‖ = ‖normalGNSRepresentation e x‖ :=
      (NonUnitalStarAlgHom.norm_map _ (normalGNSRepresentation_injective e) x).symm
    _ = ‖L.adjoint.comp ((π a).comp W)‖ := congrArg norm hx
    _ ≤ _ := weakFactorValue_norm_le π L a (ContinuousLinearMapWOT.ofCLM W)

lemma completed_averages_predual_tendsto (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L W : NormalGNS e →L[ℂ] K)
    (T : M →L[ℂ] M)
    (hT : ∀ a, normalGNSRepresentation e (T a) = L.adjoint.comp ((π a).comp W))
    (m : I → M) (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : PredualTendsto e (fun s : Finset I => ∑ i ∈ s, m i * star (m i)) atTop 1)
    (S : M →L[ℂ] M)
    (hS : ∀ a, normalGNSRepresentation e (S a) = L.adjoint.comp ((π a).comp
      (infiniteRepresentedRightAverage π (normalGNSRepresentation e) m hm W))) (a : M) :
    PredualTendsto e (fun s : Finset I => finiteRightAverage (completedRow m s) T a)
      atTop (S a) := by
  have hfac (s : Finset I) := representedRightAverage_factorization π
    (normalGNSRepresentation e) T L W hT (completedRow m s) a
  apply predual_tendsto_of_normalGNS e
    (C := ‖L‖ * ‖a‖ * ‖W‖)
  · apply Eventually.of_forall
    intro s
    exact (normal_factorization_value_norm_le e π L _ _ a (hfac s)).trans
      (mul_le_mul_of_nonneg_left
        (representedRightAverage_norm_le π (normalGNSRepresentation e) (completedRow m s)
          (completedRow_normalized m s (hm s)) W)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  · intro ξ η
    have ht := completedRow_average_tendsto π (normalGNSRepresentation e) m hm
      (normalGNS_row_limit e m hlim) W ξ
    have hv := ((L.adjoint.comp (π a)).continuous.tendsto _).comp ht
    have hinner := (tendsto_const_nhds (x := η)).inner (𝕜 := ℂ) hv
    simp only [Function.comp_def, ContinuousLinearMap.comp_apply] at hinner
    simpa only [hfac, hS, ContinuousLinearMap.comp_apply] using hinner

theorem exists_infinite_right_average (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L W : NormalGNS e →L[ℂ] K)
    (T : M →L[ℂ] M)
    (hT : ∀ a, normalGNSRepresentation e (T a) = L.adjoint.comp ((π a).comp W))
    (m : I → M) (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : PredualTendsto e (fun s : Finset I => ∑ i ∈ s, m i * star (m i)) atTop 1) :
    ∃ S : M →L[ℂ] M, ‖S‖ ≤ ‖L‖ * ‖W‖ ∧
      (∀ a, PredualTendsto e (fun s : Finset I => finiteRightAverage (completedRow m s) T a)
        atTop (S a)) ∧ weakOperatorImage e S ∈ weakRightAverageOrbit e T := by
  classical
  obtain ⟨S, hn, hS⟩ := normal_infinite_average_realize e π L W T hT m hm hlim
  have hconv := completed_averages_predual_tendsto e π L W T hT m hm hlim S hS
  refine ⟨S, hn, hconv, ?_⟩
  have ht : Tendsto (fun s : Finset I => weakOperatorImage e (finiteRightAverage (completedRow m s) T))
      atTop (𝓝 (weakOperatorImage e S)) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
    exact hconv a
  apply mem_closure_of_tendsto ht
  apply Eventually.of_forall
  intro s
  exact ⟨finiteRightAverage (completedRow m s) T,
    finiteRightAverage_mem_orbit _ (completedRow_normalized m s (hm s)) T, rfl⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
