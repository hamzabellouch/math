import OAI.Analysis.CircleDomains.Topology.QuotientTopology
import OAI.Analysis.CircleDomains.Topology.LevelQuotient

namespace OAI

/-!
# Applying finite-length level topology to the actual sphere quotient

Choose a compatible metric on `OnePoint ℂ` by its standard homeomorphism
with the unit sphere in three-dimensional Euclidean space. This keeps the
original topology definitionally unchanged. The quotient obtained from
Moore's published decomposition input then satisfies the already proved
finite-physical-length level theorem. No metric or level regularity of
the quotient is left as an additional premise.
-/

open Set Metric MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity

noncomputable def roundSphereEquiv :
    Sphere ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)

/-- A fixed compatible sphere metric, pulled back from the Euclidean
unit sphere. Its topology is the original one-point topology. -/
noncomputable abbrev sphereMetric : MetricSpace Sphere :=
  roundSphereEquiv.isEmbedding.comapMetricSpace roundSphereEquiv

attribute [local instance] sphereMetric

noncomputable abbrev sphereBorel : MeasurableSpace Sphere := borel Sphere

attribute [local instance] sphereBorel

local instance : BorelSpace Sphere := ⟨rfl⟩

theorem roundSphereEquiv_isometry : Isometry roundSphereEquiv := fun _ _ => rfl

/-- Moore's quotient on the concrete sphere, together with its complete
finite-length level consequence. The displayed Hausdorff measure is for
`sphereMetric`; all topology is the original sphere topology. -/
theorem quotientSphere_with_finite_length_levels (hMoore : MooreSphereDecomposition)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G) :
    ∃ π : Sphere → Sphere,
      Continuous π ∧ Function.Surjective π ∧
      (∀ x y, π x = π y ↔
        x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) ∧
      (∀ H : Set Sphere, IsCompact H →
        (μH[1] : Measure Sphere) ((π ⁻¹' H) ∩ G) < ∞ →
        HasFiniteLargeContinuumBound H ∧
          {C : Set H | (∃ x, C = connectedComponent x) ∧ C.Nontrivial}.Countable ∧
          ∀ C : Set H, IsCompact C → IsConnected C → LocallyConnectedSpace C) := by
  obtain ⟨π, hπ, _, hsurj, hr, _, _, hB, hTD, _⟩ :=
    quotientSphere_of_moore hMoore hG hconn
  have hdust : π '' Gᶜ ⊆ (π '' G)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    rcases (hr y x).mp heq with heq | ⟨hy', _⟩
    · exact hx (heq ▸ hy)
    · exact hy' hy
  refine ⟨π, hπ, hsurj, hr, ?_⟩
  intro H hH hlength
  exact level_topology_of_finite_physical_length π hπ hsurj
    (connected_fibers_of_component_collapse G π hsurj hr)
    hG hB hTD hdust hH hlength

end CircleDomainRigidity

end OAI
