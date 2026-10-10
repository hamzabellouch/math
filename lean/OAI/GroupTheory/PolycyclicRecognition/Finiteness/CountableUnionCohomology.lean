import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CochainExhaustion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CompatiblePrimitives
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteDimensionCohomology

namespace OAI

/-! # Cohomology above a uniform dimension bound on an exhaustive sequence

Two consecutive local vanishings suffice. The primitive-correction argument
accounts for the one extra dimension in a countable increasing union.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear

theorem cochain_primitive_of_isZero (C : CochainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (h : IsZero (C.homology (k + 1))) (z : C.X (k + 1))
    (hz : C.d (k + 1) (k + 2) z = 0) :
    ∃ y : C.X k, C.d k (k + 1) y = z := by
  have he : (C.sc' k (k + 1) (k + 2)).Exact :=
    (C.exactAt_iff' k (k + 1) (k + 2) (by simp) (by simp)).mp
      ((C.exactAt_iff_isZero_homology (k + 1)).mpr h)
  exact (ShortComplex.moduleCat_exact_iff _).mp he z hz

variable {G : Type} [Group G]

def subgroupCochainStep {H K : Subgroup G} (hHK : H ≤ K) (A : Rep ℤ G) :
    groupCohomology.inhomogeneousCochains (Rep.res K.subtype A) ⟶
      groupCohomology.inhomogeneousCochains (Rep.res H.subtype A) :=
  groupCohomology.cochainsMap (Subgroup.inclusion hHK)
    (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩)

theorem subgroupCochainStep_surjective {H K : Subgroup G} (hHK : H ≤ K)
    (A : Rep ℤ G) (k : ℕ) :
    Function.Surjective ((subgroupCochainStep hHK A).f k) := by
  change Function.Surjective (fun f : (Fin k → K) → A =>
    fun a : Fin k → H => f (fun i => Subgroup.inclusion hHK (a i)))
  apply Function.Injective.surjective_comp_right
  intro a b hab
  funext i
  exact (Subgroup.inclusion_injective hHK) (congrFun hab i)

theorem groupCohomology_isZero_of_exhaustion (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (A : Rep ℤ G) (k : ℕ)
    (hlocal₁ : ∀ n, IsZero (groupCohomology (Rep.res (S n).subtype A) (k + 1)))
    (hlocal₂ : ∀ n, IsZero (groupCohomology (Rep.res (S n).subtype A) (k + 2))) :
    IsZero (groupCohomology A (k + 2)) := by
  let C := groupCohomology.inhomogeneousCochains A
  let D (n : ℕ) := groupCohomology.inhomogeneousCochains (Rep.res (S n).subtype A)
  let R (n : ℕ) := subgroupCochainRestriction (S n) A
  let T (n : ℕ) := subgroupCochainStep (hS (Nat.le_succ n)) A
  apply HomologicalComplex.ExactAt.isZero_homology
  apply (C.exactAt_iff' (k + 1) (k + 2) (k + 3) (by simp) (by simp)).mpr
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  change C.d (k + 2) (k + 3) z = 0 at hz
  let zn (n : ℕ) := (R n).f (k + 2) z
  have hzn (n : ℕ) : (D n).d (k + 2) (k + 3) (zn n) = 0 := by
    have hc := congrArg (fun f => f z) ((R n).comm (k + 2) (k + 3))
    change (D n).d (k + 2) (k + 3) (zn n) =
      (R n).f (k + 3) (C.d (k + 2) (k + 3) z) at hc
    rw [hc, hz, map_zero]
  have hprim (n : ℕ) : ∃ y, (D n).d (k + 1) (k + 2) y = zn n :=
    cochain_primitive_of_isZero (D n) (k + 1) (hlocal₂ n) (zn n) (hzn n)
  obtain ⟨ys, hys, hcompat⟩ := exists_compatible_primitives
    (fun n => ((D n).d k (k + 1)).hom.toAddMonoidHom)
    (fun n => ((D n).d (k + 1) (k + 2)).hom.toAddMonoidHom)
    (fun n => ((T n).f k).hom.toAddMonoidHom)
    (fun n => ((T n).f (k + 1)).hom.toAddMonoidHom)
    (fun n => ((T n).f (k + 2)).hom.toAddMonoidHom)
    (fun n x => (congrArg (fun f => f x) ((T n).comm k (k + 1))).symm)
    (fun n x => (congrArg (fun f => f x) ((T n).comm (k + 1) (k + 2))).symm)
    (fun n x => by
      exact congrArg (fun f => f x) ((D n).d_comp_d k (k + 1) (k + 2)))
    (fun n y hy => cochain_primitive_of_isZero (D n) k (hlocal₁ n) y hy)
    (fun n => subgroupCochainStep_surjective (hS (Nat.le_succ n)) A k)
    zn (fun _ => rfl) hprim
  obtain ⟨y, hy⟩ := exists_cochain_of_compatible_restrictions S hS hcover A (k + 1)
    ys (fun n a => congrFun (hcompat n) a)
  refine ⟨y, ?_⟩
  change C.d (k + 1) (k + 2) y = z
  apply cochains_eq_of_exhaustive_restrictions S hS hcover A (k + 2)
  intro n
  have hc := congrArg (fun f => f y) ((R n).comm (k + 1) (k + 2))
  change (D n).d (k + 1) (k + 2) ((R n).f (k + 1) y) =
    (R n).f (k + 2) (C.d (k + 1) (k + 2) y) at hc
  rw [← hc, hy]
  exact hys n

end PolycyclicRecognition

end

end OAI
