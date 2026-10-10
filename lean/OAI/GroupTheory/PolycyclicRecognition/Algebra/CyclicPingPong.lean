import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowthPingPong

namespace OAI

/-! # The cyclic-subgroup form of ping-pong

Only images of the other attracting domains are required here. This form is
suited to higher-dimensional projective actions, whose repelling hyperplanes
need not be disjoint.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Pointwise Function

variable {G X : Type} [Group G] [MulAction G X]

theorem cyclic_ping_pong_injective (a : Bool → G) (D : Bool → Set X)
    (hne : ∀ i, (D i).Nonempty) (hdis : Pairwise (Disjoint on D))
    (hpp : ∀ i j, i ≠ j → ∀ m : ℤ, m ≠ 0 → (a i) ^ m • D j ⊆ D i) :
    Function.Injective (FreeGroup.lift a) := by
  have he : FreeGroup.lift a =
      (Monoid.CoprodI.lift fun i => FreeGroup.lift fun _ : Unit => a i).comp
        (@freeGroupEquivCoprodI Bool).toMonoidHom := by
    ext i
    simp
  rw [he, MonoidHom.coe_comp]
  apply Function.Injective.comp _ freeGroupEquivCoprodI.injective
  apply Monoid.CoprodI.lift_injective_of_ping_pong _ _ D hne hdis
  · intro i j hij
    refine FreeGroup.freeGroupUnitEquivInt.forall_congr_left.mpr ?_
    intro m hm
    change FreeGroup.lift (fun _ : Unit => a i) (FreeGroup.of () ^ m) • D j ⊆ D i
    rw [map_zpow, FreeGroup.lift_apply_of]
    apply hpp i j hij m
    intro hz
    apply hm
    simp [hz, FreeGroup.freeGroupUnitEquivInt]
  · right
    refine ⟨false, ?_⟩
    rw [FreeGroup.freeGroupUnitEquivInt.cardinal_eq, Cardinal.mk_denumerable]
    exact Cardinal.natCast_le_aleph0

theorem polynomial_growth_excludes_cyclic_ping_pong [DecidableEq G]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (a : Bool → G) (D : Bool → Set X)
    (hne : ∀ i, (D i).Nonempty) (hdis : Pairwise (Disjoint on D))
    (hpp : ∀ i j, i ≠ j → ∀ m : ℤ, m ≠ 0 → (a i) ^ m • D j ⊆ D i) : False :=
  polynomial_growth_no_free_pair S hS hgen hvol (FreeGroup.lift a)
    (cyclic_ping_pong_injective a D hne hdis hpp)

end PolycyclicRecognition

end

end OAI
