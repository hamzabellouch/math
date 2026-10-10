import OAI.Analysis.KadisonKastler.MinimalRowFamily

namespace OAI

/-! Every orbit in a minimal row family is dense in that family. -/

namespace KadisonKastler

noncomputable section

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance minimalRowDynamicsOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance minimalRowDynamicsStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem boundedWeakAlgebraMap_ext {M : VonNeumannAlgebra H} {c : ℝ}
    {F G : BoundedWeakAlgebraMap M c} (h : F.map = G.map) : F = G := by
  cases F
  cases G
  cases h
  rfl

theorem boundedWeakRowOrbit_subset_of_invariant {M : VonNeumannAlgebra H} {c : ℝ}
    (hc : 0 ≤ c) (K : Set (BoundedWeakAlgebraMap M c)) (hK : RowInvariant hc K)
    {F : BoundedWeakAlgebraMap M c} (hF : F ∈ K) : boundedWeakRowOrbit F ⊆ K := by
  intro G hG
  obtain ⟨n, r, hr, he⟩ := hG
  have he' : G = boundedWeakRowAverage hc r hr F := boundedWeakAlgebraMap_ext he
  rw [he']
  exact hK n r hr hF

theorem minimal_row_family_orbit_dense {M : VonNeumannAlgebra H} {c : ℝ}
    (hc : 0 ≤ c) (K : Set (BoundedWeakAlgebraMap M c)) (hclosed : IsClosed K)
    (hinv : RowInvariant hc K)
    (hmin : ∀ L : Set (BoundedWeakAlgebraMap M c), L ⊆ K → L.Nonempty → IsClosed L →
      RowInvariant hc L → L = K)
    {F : BoundedWeakAlgebraMap M c} (hF : F ∈ K) :
    closure (boundedWeakRowOrbit F) = K := by
  exact hmin _ (closure_minimal (boundedWeakRowOrbit_subset_of_invariant hc K hinv hF) hclosed)
    (closure_boundedWeakRowOrbit_nonempty F) isClosed_closure (rowInvariant_closure_orbit hc F)

/-- Every lower-semicontinuous quantity decreased by all row averages is
constant on a minimal invariant family. This is the norm-minimization step;
no right-module conclusion is built into it. -/
theorem minimal_row_family_quantity_constant {M : VonNeumannAlgebra H} {c : ℝ}
    (hc : 0 ≤ c) (K : Set (BoundedWeakAlgebraMap M c)) (hclosed : IsClosed K)
    (hinv : RowInvariant hc K)
    (hmin : ∀ L : Set (BoundedWeakAlgebraMap M c), L ⊆ K → L.Nonempty → IsClosed L →
      RowInvariant hc L → L = K)
    (q : BoundedWeakAlgebraMap M c → ℝ) (hsub : ∀ a, IsClosed {F | q F ≤ a})
    (hdec : ∀ (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1)
      (F : BoundedWeakAlgebraMap M c), q (boundedWeakRowAverage hc r hr F) ≤ q F)
    {F G : BoundedWeakAlgebraMap M c} (hF : F ∈ K) (hG : G ∈ K) : q F = q G := by
  have hle (A B : BoundedWeakAlgebraMap M c) (hA : A ∈ K) (hB : B ∈ K) : q B ≤ q A := by
    have hs : boundedWeakRowOrbit A ⊆ {T | q T ≤ q A} := by
      intro T hT
      obtain ⟨n, r, hr, he⟩ := hT
      have he' : T = boundedWeakRowAverage hc r hr A := boundedWeakAlgebraMap_ext he
      rw [he']
      exact hdec n r hr A
    have hcl := closure_minimal hs (hsub (q A))
    rw [minimal_row_family_orbit_dense hc K hclosed hinv hmin hA] at hcl
    exact hcl hB
  exact le_antisymm (hle G F hG hF) (hle F G hF hG)

end

end KadisonKastler

end OAI
