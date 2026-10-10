import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarConeModels
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeAmbientAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayCompactCollapse
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactLiftQuotient

namespace OAI

/-! # Concrete ray quotients and their ambient actions

The model is chosen from the previously stated nilpotent existence,
integration, and Haar inputs. Its action, section, topology and contraction
are proved properties of that choice.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter TopologicalSpace Topology
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (α₀ : H →ₗ[ℝ] ℝ)

/-- The actual integrated ray quotient, with its descended ambient action. -/
structure RayBoundaryModel where
  cone : M.MeasuredCone F (positiveWeightRay α₀)
  factorAction : F.D.carrier →* MulAut cone.Q.carrier
  action : G →* Equiv.Perm cone.Q.carrier
  equivariant : ∀ d n, factorAction d (cone.maps.quotient n) =
    cone.maps.quotient (F.action d n)
  action_eq : ∀ n d q, action (F.inclusionN n * F.inclusionD d) q =
    cone.maps.quotient n * factorAction d q
  stabilizer : ∀ g, action g 1 = 1 ↔ ∃ n d,
    n ∈ cone.maps.quotient.ker ∧ F.inclusionN n * F.inclusionD d = g

namespace RayBoundaryModel

variable {M F α₀} (R : M.RayBoundaryModel F α₀)

def sectionMap : R.cone.Q.carrier → G := fun q =>
  F.inclusionN (R.cone.maps.sectionMap q)

theorem continuous_sectionMap : Continuous R.sectionMap :=
  F.closedN.continuous.comp R.cone.maps.sectionMap.continuous

theorem section_rightInverse (q : R.cone.Q.carrier) : R.action (R.sectionMap q) 1 = q := by
  have h := R.action_eq (R.cone.maps.sectionMap q) 1 1
  simpa only [sectionMap, map_one, mul_one, R.cone.maps.section_rightInverse] using h

theorem orbit_surjective : Function.Surjective (fun g => R.action g 1) :=
  fun q => ⟨R.sectionMap q, R.section_rightInverse q⟩

theorem orbit_isQuotientMap : IsQuotientMap (fun g => R.action g 1) :=
  F.orbitMap_isQuotientMap R.cone.maps.quotient R.cone.maps.quotient_continuous
    R.cone.maps.sectionMap R.cone.maps.sectionMap.continuous
    R.cone.maps.section_rightInverse R.factorAction R.action R.action_eq

variable {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  [SimplyConnectedSpace G]
  (hExpG : IsGroupExponential ExpG)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)

include T hExpG realize hbijN hbijD dynkinN in
theorem continuous_action (g : G) : Continuous (R.action g) := by
  exact M.continuous_ambient_ray_action T F α₀ R.cone.Q R.cone.maps.expQ
    (by rw [← show R.cone.maps.chartQ = R.cone.maps.expQ from
      funext R.cone.maps.chartQ_eq]; exact R.cone.maps.chartQ.bijective)
    R.cone.maps.chartQ R.cone.maps.chartQ_eq hbijN hbijD dynkinN
    R.cone.maps.quotient R.cone.maps.quotient_exp R.factorAction R.equivariant
    (fun d => cartan_action_eq_adjoint_of_published_realization
      T M F hExpG realize hbijN hbijD dynkinN d) R.action R.action_eq g

include T hExpG realize hbijN hbijD dynkinN in
theorem contracts_compact_orbits (v : H) (hv : α₀ v < 0) :
    let ray := fun n : ℕ => ExpG (((n : ℝ) • v : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)
    (∀ n, R.action (ray n) 1 = 1) ∧ ∀ K : Set G, IsCompact K → ∀ k : ℕ → G,
      (∀ n, k n ∈ K) → Tendsto (fun n => R.action (ray n) (R.action (k n) 1))
        atTop (𝓝 1) := by
  exact M.ambient_ray_fixes_one_and_contracts_compact_orbits T F α₀
    R.cone.Q R.cone.maps.expQ
    (by rw [← show R.cone.maps.chartQ = R.cone.maps.expQ from
      funext R.cone.maps.chartQ_eq]; exact R.cone.maps.chartQ.bijective)
    R.cone.maps.chartQ R.cone.maps.chartQ_eq hbijN hbijD dynkinN
    R.cone.maps.quotient R.cone.maps.quotient_exp R.factorAction R.equivariant
    (fun d => cartan_action_eq_adjoint_of_published_realization
      T M F hExpG realize hbijN hbijD dynkinN d)
    R.cone.maps.isExpQ R.cone.maps.quotient_continuous R.action R.action_eq v hv

end RayBoundaryModel

variable [SimplyConnectedSpace G] {a : ℕ}
  (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

include T in
/-- No boundary or metric conclusion is assumed in the construction. -/
theorem nonempty_rayBoundaryModel_of_published_inputs
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (inputs : M.PolarConeModelInputs F (positiveWeightRay α₀)) (hα₀ : α₀ ≠ 0) :
    Nonempty (M.RayBoundaryModel F α₀) := by
  let C := inputs.model M F (positiveWeightRay α₀) T hExpG realize haarN
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨α, act, hα, hact, hstab, _⟩ := exists_cartan_cone_ambient_action M F T
    j ρ hρ (fun v => by rw [F.compatibleN, hmatch])
    (fun v => by rw [F.compatibleD, hmatch]) hbijN hbijD.surjective dynkinN
    (positiveWeightRay α₀) (positiveWeightRay_add α₀)
    (zero_not_mem_positiveWeightRay hα₀)
    C.maps.quotient C.maps.sectionMap C.maps.section_rightInverse C.maps.kernel_eq
  exact ⟨⟨C, α, act, hα, hact, hstab⟩⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
