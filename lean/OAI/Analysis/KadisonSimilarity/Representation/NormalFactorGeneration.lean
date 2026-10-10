import OAI.Analysis.KadisonSimilarity.Tracial.NormalTracialGeometry

namespace OAI

/-! Tracial generation by two factors implies generation of the concrete
von Neumann range by their norm-closed algebra. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry
open scoped CStarAlgebra

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)

local instance factorClosure_closed :
    IsClosed ((factorAlgebra A D).topologicalClosure : Set P) :=
  (factorAlgebra A D).isClosed_topologicalClosure

theorem normal_range_eq_generated (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra)
    (hgen : G.FactorsTraciallyGenerate A D) :
    let S := (factorAlgebra A D).topologicalClosure
    representationVonNeumannAlgebra (G.left.comp S.subtype) = M := by
  let S := (factorAlgebra A D).topologicalClosure
  let : IsClosed (S : Set P) := factorClosure_closed A D
  let σ := G.left.comp S.subtype
  let N := representationVonNeumannAlgebra σ
  have hNM : N ≤ M := by
    intro T hT
    change T ∈ representationVonNeumannAlgebra σ at hT
    rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
    rw [← SetLike.mem_coe, ← M.centralizer_centralizer]
    intro b hb
    apply hT b
    rintro _ ⟨a, rfl⟩
    apply hb
    change G.left (a : P) ∈ M.toStarSubalgebra
    rw [← hrange]
    exact ⟨(a : P), rfl⟩
  apply le_antisymm hNM
  intro T hT
  let τ := G.normalTracialRepresentation h1 hf M hrange
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange
  have hv (a : P) : Generator.Tracial.baseVector τ (e a) = G.vector a := by
    change G.left a (G.vector 1) = G.vector a
    rw [G.left_vector, mul_one]
  have hsub : Set.range (G.vector.comp (factorAlgebra A D).subtype.toLinearMap) ⊆
      subalgebraTraceVectors τ N := by
    rintro _ ⟨a, rfl⟩
    refine ⟨e (a : P), ?_, hv (a : P)⟩
    exact mem_representationVonNeumannAlgebra σ
      ⟨(a : P), (factorAlgebra A D).le_topologicalClosure a.property⟩
  exact mem_of_traceVector_mem_closure τ hNM ⟨T, hT⟩
    (closure_mono hsub (hgen (Generator.Tracial.baseVector τ ⟨T, hT⟩)))

private theorem map_generated_mem {B : Type*} [CStarAlgebra B]
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (M : VonNeumannAlgebra H)
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b, θ (σ b) ∈ M) (T : H →L[ℂ] H)
    (hT : T ∈ representationVonNeumannAlgebra σ) : θ T ∈ M := by
  rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
  rw [← SetLike.mem_coe, ← M.centralizer_centralizer]
  intro c hc
  apply θ.symm.injective
  simp only [map_mul]
  change θ.symm c * θ.symm (θ T) = θ.symm (θ T) * θ.symm c
  rw [θ.symm_apply_apply]
  apply hT (θ.symm c)
  rintro _ ⟨b, rfl⟩
  apply θ.injective
  simp only [map_mul]
  change θ (σ b) * θ (θ.symm c) = θ (θ.symm c) * θ (σ b)
  rw [θ.apply_symm_apply]
  exact hc (θ (σ b)) (hσ b)

/-- It suffices to check the two factors when conjugating the entire normal range. -/
theorem normal_range_map_mem (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra)
    (hgen : G.FactorsTraciallyGenerate A D)
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (hA : ∀ a : A, θ (G.left (a : P)) ∈ M)
    (hD : ∀ d : D, θ (G.left (d : P)) ∈ M) (x : P) :
    θ (G.left x) ∈ M := by
  let S := (factorAlgebra A D).topologicalClosure
  let : IsClosed (S : Set P) := factorClosure_closed A D
  let R := M.toStarSubalgebra.comap (θ.toStarAlgHom.comp G.left)
  have hR : IsClosed (R : Set P) :=
    (base_norm_closed M).preimage ((StarAlgEquiv.isometry θ).continuous.comp (map_continuous G.left))
  have hS : S ≤ R := by
    apply StarSubalgebra.topologicalClosure_minimal ?_ hR
    apply StarAlgebra.adjoin_le
    intro y hy
    rcases hy with hy | hy
    · exact hA ⟨y, hy⟩
    · exact hD ⟨y, hy⟩
  have hN := G.normal_range_eq_generated A D h1 hf M hrange hgen
  have hx : G.left x ∈ representationVonNeumannAlgebra (G.left.comp S.subtype) := by
    rw [hN]
    change G.left x ∈ M.toStarSubalgebra
    rw [← hrange]
    exact ⟨x, rfl⟩
  exact map_generated_mem (G.left.comp S.subtype) M θ
    (fun b => hS b.property) (G.left x) hx

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
