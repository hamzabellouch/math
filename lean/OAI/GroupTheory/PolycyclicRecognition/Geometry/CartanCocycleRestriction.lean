import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanContractedRoots
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentLieGroupNilpotent
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NilpotentReducedCohomology

namespace OAI

/-! # Reduced cocycles restricted to the actual Cartan factor

Contracted root generation identifies its fixed vectors with those of the
ambient representation. Its nilpotent Lie model is algebraically nilpotent,
so the proved reduced-cohomology theorem applies on every compact subset.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (M : CartanWordModel H) (hExpG : IsGroupExponential ExpG)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (hρ : ∀ v, Continuous (fun g => ρ g v))
  (hfix : ∀ v, (∀ g, ρ g v = v) → v = 0)

include T M hExpG realize haarN dynkinN hρ hfix in
theorem cartan_unitary_no_fixed :
    ∀ v, (∀ d : F.D.carrier, ρ (F.inclusionD d) v = v) → v = 0 := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  have hgen := M.cartan_and_contracted_generate T F hExpG realize haarN dynkinN
  have htop : (Subgroup.closure ((F.inclusionD.range : Set G) ∪
      contractedBy F.inclusionD.range)).topologicalClosure = ⊤ := by
    rw [hgen]
    exact top_unique (Subgroup.le_topologicalClosure ⊤)
  intro v hv
  apply unitary_no_fixed_on_contracting_subgroup ρ hρ hfix F.inclusionD.range htop v
  intro d
  obtain ⟨x, hx⟩ := d.property
  simpa only [hx] using hv x

variable [CompleteSpace E]

include T M hExpG realize haarN dynkinN hρ hfix in
theorem cartan_cocycle_approximation
    (b : G → E) (hbc : Continuous b) (hb : IsUnitaryCocycle ρ b)
    (Q : Set F.D.carrier) (hQ : IsCompact Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : E, ∀ d ∈ Q,
      ‖b (F.inclusionD d) + ρ (F.inclusionD d) φ - φ‖ ≤ ε := by
  let : IsTopologicalGroup F.D.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.D.modelSpace)) ⊤
  let : Group.IsNilpotent F.D.carrier := F.D.group_nilpotent inferInstance
  exact unitaryReducedVanishing_nilpotent F.D.carrier E (ρ.comp F.inclusionD)
    (cartan_unitary_no_fixed T F M hExpG realize haarN dynkinN ρ hρ hfix)
    (fun v => (hρ v).comp F.closedD.continuous) (b ∘ F.inclusionD)
    (hbc.comp F.closedD.continuous) (fun d e => by
      change b (F.inclusionD (d * e)) = _
      rw [map_mul]
      exact hb _ _) Q hQ ε hε

end PolycyclicRecognition

end

end OAI
