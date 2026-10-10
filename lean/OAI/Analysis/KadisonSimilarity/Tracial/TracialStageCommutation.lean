import OAI.Analysis.KadisonSimilarity.Tracial.NormalTracialGeometry
import OAI.Analysis.KadisonSimilarity.Tracial.GNSTracialGeometry
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixTower
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixVonNeumannRange

namespace OAI

/-! Commutation with all matrix stages extends to the represented source
by density of trace vectors in the actual normal ambient algebra. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped CStarAlgebra ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def relativeOperatorCommutant (N : VonNeumannAlgebra H) (Z : H →L[ℂ] H) :
    VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ ((N.commutant : Set (H →L[ℂ] H)) ∪ {Z})
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (Set.centralizer
      (((N.commutant : Set (H →L[ℂ] H)) ∪ {Z}) ∪
        star ((N.commutant : Set (H →L[ℂ] H)) ∪ {Z})))) = _
    exact Set.centralizer_centralizer_centralizer _

private theorem relativeOperatorCommutant_le (N : VonNeumannAlgebra H) (Z : H →L[ℂ] H) :
    relativeOperatorCommutant N Z ≤ N := by
  intro T hT
  change T ∈ StarSubalgebra.centralizer ℂ ((N.commutant : Set (H →L[ℂ] H)) ∪ {Z}) at hT
  rw [StarSubalgebra.mem_centralizer_iff] at hT
  rw [← N.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro S hS
  exact (hT S (Or.inl hS)).1

private theorem relativeOperatorCommutant_mem (N : VonNeumannAlgebra H)
    (Z T : H →L[ℂ] H) (hT : T ∈ N)
    (hZ : Z * T = T * Z) (hZstar : star Z * T = T * star Z) :
    T ∈ relativeOperatorCommutant N Z := by
  change T ∈ StarSubalgebra.centralizer ℂ ((N.commutant : Set (H →L[ℂ] H)) ∪ {Z})
  rw [StarSubalgebra.mem_centralizer_iff]
  intro S hS
  rcases hS with hS | hS
  · exact ⟨(VonNeumannAlgebra.mem_commutant_iff.mp hS T hT).symm,
      (VonNeumannAlgebra.mem_commutant_iff.mp (star_mem hS) T hT).symm⟩
  · obtain rfl := Set.mem_singleton_iff.mp hS
    exact ⟨hZ, hZstar⟩

private theorem relativeOperatorCommutant_commutes (N : VonNeumannAlgebra H)
    (Z T : H →L[ℂ] H) (hT : T ∈ relativeOperatorCommutant N Z) : Z * T = T * Z := by
  change T ∈ StarSubalgebra.centralizer ℂ ((N.commutant : Set (H →L[ℂ] H)) ∪ {Z}) at hT
  rw [StarSubalgebra.mem_centralizer_iff] at hT
  exact (hT Z (Or.inr (Set.mem_singleton Z))).1

section Source
variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder B] [StarOrderedRing B]
  (τR : R →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hB : τB 1 = 1) (trB : ∀ a b, τB (a * b) = τB (b * a))
  (hfB : ∀ a, τB (star a * a) = 0 → a = 0)
  (normalB : τB.gnsStarAlgHom.range =
    (representationVonNeumannAlgebra τB.gnsStarAlgHom).toStarSubalgebra)
  (ρ : R →⋆ₐ[ℂ] B) (hρ : ∀ a, τB (ρ a) = τR a)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))

include hB trB hfB normalB hρ M in
/-- The original GNS action commutes with every operator commuting with the stages. -/
theorem commutes_source_of_matrix_stages (Z : τB.GNS →L[ℂ] τB.GNS)
    (hZ : ∀ j a, Z * τB.gnsStarAlgHom (ρ (M.embedding j a)) =
      τB.gnsStarAlgHom (ρ (M.embedding j a)) * Z) (r : R) :
    Z * τB.gnsStarAlgHom (ρ r) = τB.gnsStarAlgHom (ρ r) * Z := by
  let G := gnsTracialGeometry τB trB
  let NB := representationVonNeumannAlgebra τB.gnsStarAlgHom
  let υ := G.normalTracialRepresentation hB (gnsTracialVector_injective τB hfB) NB normalB
  let e := equivalenceOfConcreteRange NB G.left (G.left_injective (gnsTracialVector_injective τB hfB)) normalB
  let N := relativeOperatorCommutant NB Z
  let J := gnsTracialHomIsometry τR τB ρ hρ
  have hv (b : B) : Generator.Tracial.baseVector υ (e b) = gnsTracialVector τB b := by
    change G.left b (G.vector 1) = G.vector b
    rw [G.left_vector, mul_one]
  have hstage (j : ℕ) (a : Matrix (I j) (I j) ℂ) :
      gnsTracialVector τB (ρ (M.embedding j a)) ∈ subalgebraTraceVectors υ N := by
    refine ⟨e (ρ (M.embedding j a)), ?_, hv _⟩
    apply relativeOperatorCommutant_mem NB Z _ (mem_representationVonNeumannAlgebra _ _)
      (hZ j a)
    simpa only [map_star, star_mul, star_star] using (congrArg star (hZ j (star a))).symm
  have hr : J (gnsTracialVector τR r) ∈ closure (subalgebraTraceVectors υ N) := by
    change gnsTracialVector τR r ∈ J ⁻¹' closure (subalgebraTraceVectors υ N)
    apply closure_minimal (s := ⋃ j, Set.range (fun a => gnsTracialVector τR (M.embedding j a)))
      ?_ (isClosed_closure.preimage J.continuous) (M.dense (gnsTracialVector τR r))
    intro ξ hξ
    obtain ⟨j, a, rfl⟩ := Set.mem_iUnion.mp hξ
    change gnsTracialHomIsometry τR τB ρ hρ (gnsTracialVector τR (M.embedding j a)) ∈
      closure (subalgebraTraceVectors υ N)
    rw [gnsTracialHomIsometry_vector]
    exact subset_closure (hstage j a)
  have hrr : Generator.Tracial.baseVector υ (e (ρ r)) ∈ closure (subalgebraTraceVectors υ N) := by
    rw [hv]
    change gnsTracialHomIsometry τR τB ρ hρ (gnsTracialVector τR r) ∈ _ at hr
    rwa [gnsTracialHomIsometry_vector] at hr
  have hmem := mem_of_traceVector_mem_closure υ (relativeOperatorCommutant_le NB Z)
    (e (ρ r)) hrr
  exact relativeOperatorCommutant_commutes NB Z _ hmem

include hB trB hfB normalB hρ M in
/-- Coordinate compression extends stage commutation at every finite multiplicity. -/
theorem commutes_amplified_source_of_matrix_stages (n : ℕ)
    (Y : HilbertCopies τB.GNS n →L[ℂ] HilbertCopies τB.GNS n)
    (hY : ∀ j a, commutator Y (amplify (τB.gnsStarAlgHom (ρ (M.embedding j a))) n) = 0)
    (r : R) :
    Y.comp (amplify (τB.gnsStarAlgHom (ρ r)) n) =
      (amplify (τB.gnsStarAlgHom (ρ r)) n).comp Y := by
  change Y * amplify (τB.gnsStarAlgHom (ρ r)) n = amplify (τB.gnsStarAlgHom (ρ r)) n * Y
  symm
  apply (amplify_commutes_iff_entries (τB.gnsStarAlgHom (ρ r)) Y).mpr
  intro i j
  symm
  apply commutes_source_of_matrix_stages τR τB hB trB hfB normalB ρ hρ M
    (matrixEntryCompression i j Y) ?_ r
  intro k a
  have hc : Y * amplify (τB.gnsStarAlgHom (ρ (M.embedding k a))) n =
      amplify (τB.gnsStarAlgHom (ρ (M.embedding k a))) n * Y := sub_eq_zero.mp (hY k a)
  exact ((amplify_commutes_iff_entries (τB.gnsStarAlgHom (ρ (M.embedding k a))) Y).mp
    hc.symm i j).symm

end Source
end KadisonSimilarity

end

end OAI
