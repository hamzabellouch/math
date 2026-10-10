import OAI.Analysis.KadisonKastler.SimultaneousModularCluster
import Mathlib.Topology.Ultrafilter

namespace OAI

/-! A single ultrafilter of normalized rows realizes the simultaneous
modular cluster. Every completely bounded map can be included as a coordinate. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {J : Type*} {c : J → ℝ}

local instance universalRowOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance universalRowStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem exists_simultaneous_modular_rows [Nontrivial H]
    (hc : ∀ j, 0 ≤ c j) (F : WeakMapFamily M c) :
    ∃ (ω : Ultrafilter (WeakMapFamily M c)) (n : WeakMapFamily M c → ℕ)
      (r : (A : WeakMapFamily M c) → Fin (n A) → Algebra M),
      (∀ A, ∑ i, r A i * star (r A i) = 1) ∧
      ∀ j, ∃ z : Algebra M, ∀ y ξ η, Tendsto
        (fun A => inner ℂ η ((finiteRightAverage (r A) (F j).map y : H →L[ℂ] H) ξ))
        (ω : Filter (WeakMapFamily M c))
        (𝓝 (inner ℂ η (((z * y : Algebra M) : H →L[ℂ] H) ξ))) := by
  classical
  obtain ⟨G, hG, hmod⟩ := exists_simultaneous_modular_cluster hc F
  obtain ⟨ω, hω, hlim⟩ := mem_closure_iff_ultrafilter.mp hG
  have hex (A : WeakMapFamily M c) : ∃ (n : ℕ) (r : Fin n → Algebra M)
      (hr : ∑ i, r i * star (r i) = 1),
      A ∈ familyRowOrbit hc F → A = familyRowAverage hc r hr F := by
    by_cases hA : A ∈ familyRowOrbit hc F
    · obtain ⟨n, r, hr, he⟩ := hA
      exact ⟨n, r, hr, fun _ => he⟩
    · exact ⟨1, fun _ => 1, by simp, fun h => (hA h).elim⟩
  choose n r hr he using hex
  have ht : Tendsto (fun A => familyRowAverage hc (r A) (hr A) F)
      (ω : Filter (WeakMapFamily M c)) (𝓝 G) := by
    apply (tendsto_id'.mpr hlim).congr'
    filter_upwards [hω] with A hA
    exact he A hA
  refine ⟨ω, n, r, hr, ?_⟩
  intro j
  refine ⟨(G j).map 1, ?_⟩
  intro y ξ η
  have hcbase : Continuous (boundedWeakAlgebraCoefficients (M := M) (c := c j)) :=
    continuous_induced_dom
  have hcfs : Continuous (fun A : WeakMapFamily M c =>
      boundedWeakAlgebraCoefficients (A j) (y, ξ, η)) :=
    ((continuous_apply (y, ξ, η)).comp hcbase).comp (continuous_apply j)
  have h := (hcfs.tendsto G).comp ht
  change Tendsto (fun A => inner ℂ η ((finiteRightAverage (r A) (F j).map y : H →L[ℂ] H) ξ))
    (ω : Filter (WeakMapFamily M c))
    (𝓝 (inner ℂ η ((((G j).map y : Algebra M) : H →L[ℂ] H) ξ))) at h
  rw [right_module_eq_left_multiplication (G j).map (hmod j) y] at h
  exact h

structure BoundedMapDatum (M : VonNeumannAlgebra H) where
  bound : ℝ
  nonneg : 0 ≤ bound
  map : Algebra M →ₗ[ℂ] Algebra M
  bounded : CompletelyBoundedBy map bound

abbrev UniversalMapFamily (M : VonNeumannAlgebra H) :=
  WeakMapFamily M (fun j : BoundedMapDatum M => j.bound)

theorem exists_universal_modular_rows [Nontrivial H] (M : VonNeumannAlgebra H) :
    ∃ (ω : Ultrafilter (UniversalMapFamily M)) (n : UniversalMapFamily M → ℕ)
      (r : (A : UniversalMapFamily M) → Fin (n A) → Algebra M),
      (∀ A, ∑ i, r A i * star (r A i) = 1) ∧
      ∀ (F : Algebra M →ₗ[ℂ] Algebra M) (d : ℝ), 0 ≤ d → CompletelyBoundedBy F d →
        ∃ z : Algebra M, ∀ y ξ η, Tendsto
          (fun A => inner ℂ η ((finiteRightAverage (r A) F y : H →L[ℂ] H) ξ))
          (ω : Filter (UniversalMapFamily M))
          (𝓝 (inner ℂ η (((z * y : Algebra M) : H →L[ℂ] H) ξ))) := by
  let F : UniversalMapFamily M := fun j => ⟨j.map, j.bounded⟩
  obtain ⟨ω, n, r, hr, hm⟩ := exists_simultaneous_modular_rows
    (fun j : BoundedMapDatum M => j.nonneg) F
  exact ⟨ω, n, r, hr, fun A d hd hA => hm ⟨d, hd, A, hA⟩⟩

end

end KadisonKastler

end OAI
