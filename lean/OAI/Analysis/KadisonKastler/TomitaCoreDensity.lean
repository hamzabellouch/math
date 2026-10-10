import OAI.Analysis.KadisonKastler.TomitaCoreCoordinates

namespace OAI

/-! # Density of the algebraic polar graph coordinates -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem tomitaCoreCoordinate_dense (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    DenseRange (tomitaCoreCoordinate J Ω hsep hcyc) := by
  intro x
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let U := tomitaPolarCoordinates J Ω hsep hcyc
  have hx : (U x).val ∈ closure (Set.range (rescaledGraphMap M J Ω 1)) := (U x).property
  obtain ⟨v,⟨a,rfl⟩,ha⟩ := (Metric.mem_closure_iff.mp hx) ε hε
  refine ⟨tomitaCoreCoordinate J Ω hsep hcyc a,⟨a,rfl⟩,?_⟩
  rw [← U.dist_map]
  change dist (U x).val (U (tomitaCoreCoordinate J Ω hsep hcyc a)).val < ε
  rw [tomitaCoreCoordinate_graph]
  exact ha

end

end KadisonKastler

end OAI
