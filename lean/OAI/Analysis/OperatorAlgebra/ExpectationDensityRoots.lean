import OAI.Analysis.OperatorAlgebra.FiniteVectorDensityTensor
import OAI.Analysis.OperatorAlgebra.ExpectationFiniteDensity

namespace OAI

/-! Application of the hypertrace separation and Powers–Størmer estimates
to an actual completely positive expectation. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

open scoped TensorProduct

theorem densityRoot_finite_support {E H : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (z : E ⊗[ℂ] H) :
    ∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧
      ∀ x, NuclearUltrapower.hsOperator (NuclearUltrapower.densityRoot z) x ∈ F := by
  obtain ⟨F, hF, hFz⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    ({z} : Set (E ⊗[ℂ] H)) (Set.finite_singleton z)
  let : FiniteDimensional ℂ F := hF
  obtain ⟨w, hw⟩ := hFz (Set.mem_singleton z)
  have hm : TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) F.subtypeₗᵢ w = z := hw
  refine ⟨F, hF, ?_⟩
  intro x
  rw [← hm, NuclearUltrapower.densityRoot_mapIsometry, NuclearUltrapower.hsOperator_coe,
    NuclearUltrapower.tensorOperator_liftOperatorTensor]
  exact Subtype.property _

variable {H I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype I] [Fintype J]

/-- A finite tracial expectation supplies positive finite-rank density roots
of norm at most one, approximately invariant under the prescribed unitaries. -/
theorem expectation_finite_density_roots (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
    (hEf : ∀ T, T ∈ M → E T = T)
    (a : I → selfAdjoint M.toStarSubalgebra) (u : J → unitary M.toStarSubalgebra)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (x : Fin n → H),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k = 1) ∧ (∀ k, ‖x k‖ ≤ 1) ∧
      (∀ i, |(τ.functional (a i)).re -
        ∑ k, w k * (inner ℂ (x k) (((a i : M.toStarSubalgebra) : H →L[ℂ] H) (x k))).re| < ε) ∧
      let z := NuclearUltrapower.densityRoot (finiteVectorDensityTensor w x)
      ‖z‖ ≤ 1 ∧ 0 ≤ NuclearUltrapower.hsOperator z ∧
        (∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧
          ∀ y, NuclearUltrapower.hsOperator z y ∈ F) ∧
        ∀ j, ‖NuclearUltrapower.hsConjugation
          (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) z - z‖ ^ 2 < ε := by
  obtain ⟨n, w, x, hw, hws, hx, ha, hu⟩ :=
    expectation_finite_density M τ E hE hEr hEf a u hε
  refine ⟨n, w, x, hw, hws, hx, ha, ?_⟩
  dsimp only
  refine ⟨?_, ?_, densityRoot_finite_support _, ?_⟩
  · rw [NuclearUltrapower.densityRoot_norm]
    exact finiteVectorDensityTensor_norm_le_one w hw hws x hx
  · rw [NuclearUltrapower.hsOperator_densityRoot]
    exact CFC.sqrt_nonneg _
  · intro j
    exact (finiteVectorDensity_root_central w hw x
      (subalgebraUnitaryIsometry M.toStarSubalgebra (u j))).trans_lt (hu j)

end WeakPureInfiniteness

end

end OAI
