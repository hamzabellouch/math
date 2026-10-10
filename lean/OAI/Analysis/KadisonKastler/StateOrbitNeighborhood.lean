import OAI.Analysis.KadisonKastler.StateOrbitCompact

namespace OAI

/-! # Neighborhood control by asymptotic state-central hulls -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_stateOrbitHull_subset_open (ξ : H) (a : Algebra M)
    {U : Set (H →WOT[ℂ] H)} (hU : IsOpen U) (hcore : stateOrbitCore ξ a ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ closedConvexHull ℝ (stateUnitaryOrbit ξ a δ) ⊆ U := by
  let I := {δ : ℝ // 0 < δ}
  let t : I → Set (H →WOT[ℂ] H) :=
    fun δ => closedConvexHull ℝ (stateUnitaryOrbit ξ a δ.val)
  let K := closedConvexHull ℝ (stateUnitaryOrbit ξ a 1) ∩ Uᶜ
  let : Nonempty I := ⟨⟨1,zero_lt_one⟩⟩
  have hK : IsCompact K := (stateOrbitHull_compact ξ a 1).inter_right hU.isClosed_compl
  have hdis : Disjoint K (⋂ δ : I, t δ) := by
    apply Set.disjoint_left.mpr
    intro T hTK hT
    apply hTK.2
    apply hcore
    intro δ hδ
    exact Set.mem_iInter.mp hT ⟨δ,hδ⟩
  have hdir : Directed (· ⊇ ·) t := by
    intro δ ε
    refine ⟨⟨min δ.val ε.val,lt_min δ.property ε.property⟩,?_,?_⟩
    · exact stateOrbitHull_mono ξ a (min_le_left _ _)
    · exact stateOrbitHull_mono ξ a (min_le_right _ _)
  obtain ⟨δ,hδ⟩ := hK.elim_directed_family_closed t (fun _ => isClosed_closedConvexHull)
    hdis hdir
  refine ⟨min δ.val 1,lt_min δ.property zero_lt_one,?_⟩
  intro T hT
  by_contra hnot
  apply Set.disjoint_left.mp hδ (show T ∈ K from
    ⟨stateOrbitHull_mono ξ a (min_le_right _ _) hT,hnot⟩)
  exact stateOrbitHull_mono ξ a (min_le_left _ _) hT

end

end KadisonKastler

end OAI
