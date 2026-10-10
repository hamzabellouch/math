import OAI.Analysis.KadisonSimilarity.Tracial.TracialGeneratedNormalClosure

namespace OAI

/-! A closed star subalgebra of a finite von Neumann algebra generates
exactly the bounded elements in the closure of its trace vectors. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance ambient_closed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  base_norm_closed M

variable (S : StarSubalgebra ℂ M.toStarSubalgebra) [IsClosed (S : Set M.toStarSubalgebra)]

def tracialSeedRepresentation : S →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  M.toStarSubalgebra.subtype.comp S.subtype

def tracialSeedVonNeumann : VonNeumannAlgebra H :=
  representationVonNeumannAlgebra (tracialSeedRepresentation S)

theorem tracialSeedVonNeumann_le : tracialSeedVonNeumann S ≤ M := by
  intro T hT
  change T ∈ representationVonNeumannAlgebra (tracialSeedRepresentation S) at hT
  rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
  rw [← SetLike.mem_coe, ← M.centralizer_centralizer]
  intro b hb
  apply hT b
  rintro _ ⟨a, rfl⟩
  exact hb _ a.val.property

theorem seed_mem_tracialSeedVonNeumann (a : S) :
    ((a : M.toStarSubalgebra) : H →L[ℂ] H) ∈ tracialSeedVonNeumann S :=
  mem_representationVonNeumannAlgebra (tracialSeedRepresentation S) a

theorem normal_mem_iff_traceVector_mem_seed_closure (τ : TracialRepresentation M)
    (x : M.toStarSubalgebra) :
    (x : H →L[ℂ] H) ∈ tracialSeedVonNeumann S ↔
      baseVector τ x ∈ closure (baseVector τ '' (S : Set M.toStarSubalgebra)) := by
  constructor
  · intro hx
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a, _, ha, _⟩ := twoVectorKaplanskyInput (tracialSeedRepresentation S)
      (x : H →L[ℂ] H) hx τ.vector τ.vector (ε / 2) (by positivity)
    refine ⟨baseVector τ (a : M.toStarSubalgebra), ⟨a, a.property, rfl⟩, ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    exact ha.trans_lt (by linarith)
  · intro hx
    apply mem_of_traceVector_mem_closure τ (tracialSeedVonNeumann_le S) x
    apply closure_mono _ hx
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, seed_mem_tracialSeedVonNeumann S ⟨a, ha⟩, rfl⟩

end KadisonSimilarity

end

end OAI
