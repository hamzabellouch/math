import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorSymbol

namespace OAI

/-! # Partial Cartesian symbols and their compactly supported Schwartz derivatives -/

open Set
open scoped SchwartzMap LineDeriv

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousPartialSymbol (N : ℕ) (j : Fin N → Fin 12)
    (s : Finset (Fin N)) (ξ : E) : ℂ := ∏ i ∈ s, ((ξ (j i) : ℂ) * Complex.I)

theorem homogeneousOrderedSymbol_add (N : ℕ) (j : Fin N → Fin 12) (ξ η : E) :
    homogeneousOrderedSymbol N j (ξ + η) =
      ∑ s : Finset (Fin N), homogeneousPartialSymbol N j s ξ *
        homogeneousPartialSymbol N j sᶜ η := by
  simp only [homogeneousOrderedSymbol, homogeneousPartialSymbol, PiLp.add_apply,
    Complex.ofReal_add, add_mul]
  exact Fintype.prod_add _ _

theorem exists_schwartzPartialDerivative (N : ℕ) (j : Fin N → Fin 12)
    (s : Finset (Fin N)) (K : 𝓢(E, ℂ)) :
    ∃ G : 𝓢(E, ℂ),
      (∀ ξ : E, radianFourierKernel G ξ = homogeneousPartialSymbol N j s ξ * radianFourierKernel K ξ) ∧
      tsupport (G : E → ℂ) ⊆ tsupport (K : E → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨K, ?_, subset_rfl⟩
      intro ξ
      simp [homogeneousPartialSymbol]
  | @insert i s hi ih =>
      obtain ⟨G, hG, hsup⟩ := ih
      refine ⟨∂_{(EuclideanSpace.basisFun (Fin 12) ℝ) (j i)} G, ?_, ?_⟩
      · intro ξ
        rw [radianFourierKernel_lineDeriv, hG]
        simp only [EuclideanSpace.inner_basisFun_real, homogeneousPartialSymbol,
          Finset.prod_insert hi]
        ring
      · exact (SchwartzMap.tsupport_lineDerivOp_subset _ G).trans hsup

theorem exists_compact_schwartzPartialDerivative (N : ℕ) (j : Fin N → Fin 12)
    (s : Finset (Fin N)) (K : 𝓢(E, ℂ)) (R : ℝ)
    (hK : ∀ x : E, R < ‖x‖ → K x = 0) :
    ∃ G : 𝓢(E, ℂ),
      (∀ ξ : E, radianFourierKernel G ξ = homogeneousPartialSymbol N j s ξ * radianFourierKernel K ξ) ∧
      (∀ x : E, R < ‖x‖ → G x = 0) := by
  obtain ⟨G, hG, hsup⟩ := exists_schwartzPartialDerivative N j s K
  refine ⟨G, hG, ?_⟩
  have hball : tsupport (K : E → ℂ) ⊆ Metric.closedBall (0 : E) R := by
    apply closure_minimal ?_ Metric.isClosed_closedBall
    intro x hx
    have hh : ‖x‖ ≤ R := le_of_not_gt (fun h => hx (hK x h))
    simpa only [Metric.mem_closedBall, dist_zero_right] using hh
  intro x hx
  by_contra hGx
  have hb := hball (hsup (subset_closure hGx))
  have hh : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  exact (not_le_of_gt hx) hh

end DefocusingNLS

end OAI
