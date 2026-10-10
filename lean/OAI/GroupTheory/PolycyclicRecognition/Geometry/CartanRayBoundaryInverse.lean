import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRayBoundaryModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryFamilyHomeomorphism

namespace OAI

/-! # Inverse boundary families on concrete Cartan quotients -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G P : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- The actual quotient contraction supplies both inverse identities. -/
theorem ray_boundary_homeomorphisms_of_compact_shadows
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (αS αT : H →ₗ[ℝ] ℝ) (RS : M.RayBoundaryModel F αS) (RT : M.RayBoundaryModel F αT)
    (vS vT : H) (hvS : αS vS < 0) (hvT : αT vT < 0)
    (B : P → RS.cone.Q.carrier → RT.cone.Q.carrier)
    (C : P → RT.cone.Q.carrier → RS.cone.Q.carrier)
    (hBcont : ∀ p, Continuous (B p)) (hCcont : ∀ p, Continuous (C p))
    (f g : P → G → G) {Lf Lg ef eg E : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ Lf * dist x y + ef)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ Lg * dist x y + eg)
    (hgf : ∀ p x, dist (g p (f p x)) x ≤ E)
    (hfg : ∀ p x, dist (f p (g p x)) x ≤ E)
    (KS : Set RS.cone.Q.carrier) (KT : Set RT.cone.Q.carrier)
    (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hB : ∀ p x, ∃ z ∈ KT, B p (RS.action x 1) = RT.action (f p x) z)
    (hC : ∀ p x, ∃ z ∈ KS, C p (RT.action x 1) = RS.action (g p x) z) :
    ∃ D : P → RS.cone.Q.carrier ≃ₜ RT.cone.Q.carrier,
      (∀ p q, D p q = B p q) ∧ (∀ p q, (D p).symm q = C p q) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  obtain ⟨hfixS, hcS⟩ := RS.contracts_compact_orbits T hExpG realize hbijN hbijD dynkinN vS hvS
  obtain ⟨hfixT, hcT⟩ := RT.contracts_compact_orbits T hExpG realize hbijN hbijD dynkinN vT hvT
  exact boundary_family_homeomorphisms_of_compact_shadows
    RS.action RT.action (RS.continuous_action T hExpG realize hbijN hbijD dynkinN)
    (RT.continuous_action T hExpG realize hbijN hbijD dynkinN)
    RS.sectionMap RS.continuous_sectionMap RS.section_rightInverse
    RT.sectionMap RT.continuous_sectionMap RT.section_rightInverse
    _ _ hfixS hfixT hcS hcT B C hBcont hCcont f g hLf hLg hf hg hgf hfg
    KS KT hKS hKT hB hC

end PolycyclicRecognition.CartanWordModel

end

end OAI
