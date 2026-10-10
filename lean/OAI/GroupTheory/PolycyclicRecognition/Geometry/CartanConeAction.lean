import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeInvariance
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorQuotientAction

namespace OAI

/-! # The cone quotient action for the actual overlapping Cartan factors -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  {EN N Q : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [Group Q]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N)
  (hExpN : IsGroupExponential ExpN) (hbij : Function.Bijective ExpN)
  (dynkin : NilpotentDynkinExpansionInput EN N)

omit M T hExpN dynkin [FiniteDimensional ℝ L] [T2Space N] in
include hbij in
/-- In exponential coordinates the actual quotient kernel is exactly the
given linear ideal. -/
theorem mem_kernel_exp_iff
    (I : LieIdeal ℝ (cartanRootIdeal H)) (π : N →* Q)
    (hker : (π.ker : Set N) = ExpN '' (eN '' (I : Set (cartanRootIdeal H))))
    (v : cartanRootIdeal H) : ExpN (eN v) ∈ π.ker ↔ v ∈ I := by
  change ExpN (eN v) ∈ (π.ker : Set N) ↔ v ∈ I
  rw [hker]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, he⟩
    exact eN.injective (hbij.injective he) ▸ hw
  · intro hv
    exact ⟨eN v, ⟨v, hv, rfl⟩, rfl⟩

/-- The genuine adjoint group automorphism preserves the actual quotient
kernel. No extra invariance hypothesis about the group is required. -/
theorem cone_kernel_adjoint_invariant
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (π : N →* Q)
    (hker : (π.ker : Set N) = ExpN '' (eN '' (M.coneWordIdeal C : Set (cartanRootIdeal H))))
    (h : H) (g : N) :
    M.adjointGroupAutomorphism T eN ExpN hExpN hbij dynkin h g ∈ π.ker ↔ g ∈ π.ker := by
  obtain ⟨v, rfl⟩ := (hbij.comp eN.bijective).surjective g
  change integrateNilpotentLieEquiv eN ExpN hbij dynkin hExpN M.bound_zero
    (cartanIdealAdjointAutomorphism T H h) (ExpN (eN v)) ∈ π.ker ↔ _
  rw [integrateNilpotentLieEquiv_apply_exp]
  change ExpN (eN (cartanIdealAdjointAutomorphism T H h v)) ∈ π.ker ↔
    ExpN (eN v) ∈ π.ker
  rw [mem_kernel_exp_iff eN ExpN hbij (M.coneWordIdeal C) π hker,
    mem_kernel_exp_iff eN ExpN hbij (M.coneWordIdeal C) π hker]
  exact M.coneWordIdeal_adjoint_mem_iff T C hadd h v

end CartanWordModel

section ActualFactors

variable {EG G Q : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [Group Q]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The already proved exact overlap of the actual factors is killed by
the cone quotient, because its logarithm is in the zero weight space. -/
theorem cartan_factor_overlap_killed
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (hzero : (0 : H →ₗ[ℝ] ℝ) ∉ C)
    (π : F.N.carrier →* Q)
    (hπ : ∀ v : cartanRootIdeal H,
      π (F.ExpN (F.N.equiv v)) = 1 ↔ v ∈ M.coneWordIdeal C)
    (n : F.N.carrier) (d : F.D.carrier) (he : F.inclusionN n = F.inclusionD d) :
    π n = 1 := by
  have hg : F.inclusionN n ∈ Set.range F.inclusionN ∩ Set.range F.inclusionD :=
    ⟨⟨n, rfl⟩, ⟨d, he.symm⟩⟩
  rw [F.overlap] at hg
  obtain ⟨v, ⟨hvN, hvH⟩, hv⟩ := hg
  let x : cartanRootIdeal H := ⟨v, hvN⟩
  have hn : F.ExpN (F.N.equiv x) = n :=
    F.closedN.injective ((F.compatibleN x).trans hv)
  rw [← hn]
  exact (hπ x).mpr (M.cartan_intersection_mem_coneWordIdeal C hadd hzero x hvH)

variable {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

include T in
/-- Faithful exponential compatibility identifies the actual factor action
with the adjoint automorphism, so its cone kernel invariance is derived. -/
theorem cartan_factor_cone_kernel_invariant
    (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ)
    (hN : ∀ x : cartanRootIdeal H,
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h))
    (hNbij : Function.Bijective F.ExpN) (hDsurj : Function.Surjective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (π : F.N.carrier →* Q)
    (hker : (π.ker : Set F.N.carrier) =
      F.ExpN '' (F.N.equiv '' (M.coneWordIdeal C : Set (cartanRootIdeal H))))
    (d : F.D.carrier) (n : F.N.carrier) : F.action d n ∈ π.ker ↔ n ∈ π.ker := by
  obtain ⟨h, rfl⟩ := (hDsurj.comp F.D.equiv.surjective) d
  have he : F.action (F.ExpD (F.D.equiv h)) n =
      M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hNbij dynkin h n := by
    apply F.closedN.injective
    rw [F.conjugation]
    exact (M.adjointGroupAutomorphism_eq_conjugation T F.N.equiv F.ExpN F.isExpN hNbij
      dynkin j ρ hρ F.inclusionN (fun h => F.inclusionD (F.ExpD (F.D.equiv h))) hN hD h n).symm
  change F.action (F.ExpD (F.D.equiv h)) n ∈ π.ker ↔ n ∈ π.ker
  rw [he]
  exact M.cone_kernel_adjoint_invariant T F.N.equiv F.ExpN F.isExpN hNbij dynkin C hadd π hker h n

end ActualFactors
end PolycyclicRecognition

end

end OAI
