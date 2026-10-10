import OAI.Analysis.KadisonKastler.MinimalFamilyDiagonalNorm

namespace OAI

/-! Every member of a minimal row family in a fixed completely bounded
orbit closure is right modular. The auxiliary factorization is constructed
before applying the central-support localization argument. -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {c : ℝ}

local instance minimalModuleOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance minimalModuleStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem minimal_row_family_right_module_of_factorization
    (hc : 0 ≤ c) (F₀ : BoundedWeakAlgebraMap M c)
    (C : Set (BoundedWeakAlgebraMap M c))
    (hC : C ⊆ closure (boundedWeakRowOrbit F₀)) (hclosed : IsClosed C)
    (hinv : RowInvariant hc C)
    (hmin : ∀ D : Set (BoundedWeakAlgebraMap M c), D ⊆ C → D.Nonempty → IsClosed D →
      RowInvariant hc D → D = C)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R₀ : H →L[ℂ] K)
    (hF₀ : ∀ a, (F₀.map a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R₀)) :
    ∀ G ∈ C, ∀ a b, G.map (a * b) = G.map a * b := by
  have hex (G : C) : ∃ S : H →L[ℂ] factorizationCyclicSpace π L,
      ‖S‖ ≤ ‖R₀‖ ∧ ∀ a, (G.val.map a : H →L[ℂ] H) =
        (cyclicFactorLeft π L).adjoint.comp ((cyclicFactorRepresentation π L a).comp S) :=
    (exists_unique_cyclic_factor_of_mem_orbitClosure π L R₀ F₀ hF₀ (hC G.property)).exists
  choose R hR using hex
  have hcont := continuous_cyclic_right_factor π L C ‖R₀‖ (norm_nonneg _) R
    (fun G => (hR G).1) (fun G => (hR G).2)
  have hrow (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1) (G : C) :
      R ⟨boundedWeakRowAverage hc r hr G.val, hinv n r hr G.property⟩ =
        representationRowAverage (cyclicFactorRepresentation π L) r (R G) := by
    apply cyclic_right_factor_row_average π L (R G) _ G.val.map (hR G).2 r
    exact (hR ⟨boundedWeakRowAverage hc r hr G.val, hinv n r hr G.property⟩).2
  intro G hG
  let F : Algebra M →L[ℂ] Algebra M := G.map.mkContinuous c G.bound.apply_norm_le
  exact right_module_of_factor_diagonal_norm (cyclicFactorRepresentation π L)
    (cyclicFactorLeft π L) (R ⟨G, hG⟩) F (hR ⟨G, hG⟩).2
    (minimal_row_family_diagonal_norm hc C hclosed hinv hmin
      (cyclicFactorRepresentation π L) R hcont hrow ⟨G, hG⟩)

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
theorem minimal_row_family_right_module [Nontrivial H]
    (hc : 0 ≤ c) (F₀ : BoundedWeakAlgebraMap M c)
    (C : Set (BoundedWeakAlgebraMap M c))
    (hC : C ⊆ closure (boundedWeakRowOrbit F₀)) (hclosed : IsClosed C)
    (hinv : RowInvariant hc C)
    (hmin : ∀ D : Set (BoundedWeakAlgebraMap M c), D ⊆ C → D.Nonempty → IsClosed D →
      RowInvariant hc D → D = C) :
    ∀ G ∈ C, ∀ a b, G.map (a * b) = G.map a * b := by
  obtain ⟨D⟩ := exists_row_operator_factorization F₀.map
    (show 0 < c + 1 by linarith) (F₀.bound.mono (by linarith : c ≤ c + 1))
  exact minimal_row_family_right_module_of_factorization hc F₀ C hC hclosed hinv hmin
    D.representation D.leftMap D.rightMap D.factorization

end

end KadisonKastler

end OAI
