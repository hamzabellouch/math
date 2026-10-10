import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeAction

namespace OAI

/-! # The ambient action on the actual cone quotient

The algebraic ideal and its integrated kernel determine the action and its
stabilizer. No injective product decomposition of the ambient group is used.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {EG G Q : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [Group Q]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

include T in
/-- The constructed nilpotent quotient carries the ambient action in the
cone-quotient lemma, with exact equivariance and stabilizer. -/
theorem exists_cartan_cone_ambient_action
    (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ)
    (hN : ∀ x : cartanRootIdeal H,
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h))
    (hNbij : Function.Bijective F.ExpN) (hDsurj : Function.Surjective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (hzero : (0 : H →ₗ[ℝ] ℝ) ∉ C)
    (π : F.N.carrier →* Q) (s : Q → F.N.carrier) (hs : Function.RightInverse s π)
    (hker : (π.ker : Set F.N.carrier) =
      F.ExpN '' (F.N.equiv '' (M.coneWordIdeal C : Set (cartanRootIdeal H)))) :
    ∃ (α : F.D.carrier →* MulAut Q) (act : G →* Equiv.Perm Q),
      (∀ d n, α d (π n) = π (F.action d n)) ∧
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = π n * α d q) ∧
      (∀ g, act g 1 = 1 ↔ ∃ n d, n ∈ π.ker ∧ F.inclusionN n * F.inclusionD d = g) ∧
      ∀ g h, act (g * h) 1 = act g (act h 1) := by
  have ha := cartan_factor_cone_kernel_invariant M F T j ρ hρ hN hD hNbij hDsurj
    dynkin C hadd π hker
  have hkill : ∀ n d, F.inclusionN n = F.inclusionD d → π n = 1 := by
    apply cartan_factor_overlap_killed M F C hadd hzero π
    intro v
    exact CartanWordModel.mem_kernel_exp_iff F.N.equiv F.ExpN hNbij (M.coneWordIdeal C) π hker v
  obtain ⟨act, hact, hstab, heq⟩ := exists_descended_factor_quotient_action
    F.inclusionN F.inclusionD F.closedN.injective F.action F.conjugation F.surjective
    π s hs ha hkill
  exact ⟨descendQuotientAction π s hs F.action ha, act,
    descendQuotientAction_project π s hs F.action ha, hact, hstab, heq⟩

end PolycyclicRecognition

end

end OAI
