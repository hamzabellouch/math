import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubgroupShapiroReturn
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalModuleFunctor

namespace OAI

/-! # Rational surjectivity from a finite-index subgroup

The actual Shapiro transfer followed by inclusion is multiplication by the
subgroup index. Rationalization therefore makes inclusion surjective in every
degree, with arbitrary coefficients restricted from the ambient group.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule Finsupp.module
variable {G : Type} [Group G]

theorem homology_map_nsmul_identity (A : Rep ℤ G) (m n : ℕ) :
    groupHomology.map (MonoidHom.id G) (m • (𝟙 A)) n =
      m • (𝟙 (groupHomology A n)) := by
  have hc : groupHomology.chainsMap (MonoidHom.id G) (m • (𝟙 A)) =
      m • (𝟙 (groupHomology.inhomogeneousChains A)) := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    rw [groupHomology.chainsMap_id_f_hom_eq_mapRange]
    change Finsupp.mapRange.linearMap ((m • (𝟙 A)).hom.toLinearMap) = m • LinearMap.id
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Rep.nsmul_hom,
      LinearMap.smul_apply, LinearMap.id_apply]
    change Finsupp.single x (m • a) = m • Finsupp.single x a
    exact map_nsmul (Finsupp.singleAddHom x) m a
  let F := homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n
  change F.map _ = m • (𝟙 (F.obj (groupHomology.inhomogeneousChains A)))
  rw [hc, Functor.map_nsmul]
  exact congrArg (fun f => m • f) (F.map_id _)

def finiteIndexHomologyTransfer (H : Subgroup G) [H.FiniteIndex]
    (A : Rep ℤ G) (n : ℕ) :
    groupHomology A n ⟶ groupHomology (Rep.res H.subtype A) n :=
  groupHomology.map (MonoidHom.id G) (finiteIndexLift H A) n ≫
    (subgroupShapiroIso H (Rep.res H.subtype A) n).inv

theorem finiteIndexHomologyTransfer_inclusion (H : Subgroup G) [H.FiniteIndex]
    (A : Rep ℤ G) (n : ℕ) :
    finiteIndexHomologyTransfer H A n ≫ subgroupHomologyInclusion H A n =
      H.index • (𝟙 (groupHomology A n)) := by
  rw [finiteIndexHomologyTransfer, Category.assoc,
    ← subgroupShapiro_return H A n, Iso.inv_hom_id_assoc,
    ← groupHomology.map_id_comp, finiteIndexLift_return, homology_map_nsmul_identity]

theorem rational_finiteIndex_homology_surjective (H : Subgroup G) [H.FiniteIndex]
    (A : Rep ℤ G) (n : ℕ) :
    Function.Surjective ((subgroupHomologyInclusion H A n).hom.baseChange ℚ) := by
  let f := (subgroupHomologyInclusion H A n).hom.baseChange ℚ
  let t := (finiteIndexHomologyTransfer H A n).hom.baseChange ℚ
  have hi : (H.index : ℚ) ≠ 0 := by
    exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := H))
  have ht (x : groupHomology A n) :
      (subgroupHomologyInclusion H A n) (finiteIndexHomologyTransfer H A n x) =
        H.index • x := by
    exact congrArg (fun k => k.hom x) (finiteIndexHomologyTransfer_inclusion H A n)
  have hft : ∀ x, f (t x) = (H.index : ℚ) • x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
      change (subgroupHomologyInclusion H A n).hom.baseChange ℚ
        ((finiteIndexHomologyTransfer H A n).hom.baseChange ℚ (a ⊗ₜ[ℤ] x)) = _
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, ht]
      have hm : ∀ m : ℕ, a ⊗ₜ[ℤ] (m • x) = (m : ℚ) • (a ⊗ₜ[ℤ] x) := by
        intro m
        induction m with
        | zero => simp only [TensorProduct.tmul_zero, Nat.cast_zero, zero_smul]
        | succ m ih =>
          rw [succ_nsmul, TensorProduct.tmul_add, ih, Nat.cast_add, Nat.cast_one,
            add_smul, one_smul]
      exact hm H.index
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  intro x
  refine ⟨(H.index : ℚ)⁻¹ • t x, ?_⟩
  rw [map_smul, hft, smul_smul, inv_mul_cancel₀ hi, one_smul]

theorem rational_nestedSubgroup_homology_surjective {H K : Subgroup G} (hHK : H ≤ K)
    [(H.subgroupOf K).FiniteIndex] (A : Rep ℤ G) (n : ℕ) :
    Function.Surjective ((groupHomology.map (Subgroup.inclusion hHK)
      (subgroupRestrictionMap hHK A) n).hom.baseChange ℚ) := by
  let e := (Subgroup.subgroupOfEquivOfLe hHK).symm
  let s := groupHomology.mapIso (A := Rep.res H.subtype A)
    (B := Rep.res (H.subgroupOf K).subtype (Rep.res K.subtype A)) e
    (LinearEquiv.refl ℤ A.V) (by intro g; rfl) n
  have hs : s.hom ≫ subgroupHomologyInclusion (H.subgroupOf K) (Rep.res K.subtype A) n =
      groupHomology.map (Subgroup.inclusion hHK) (subgroupRestrictionMap hHK A) n := by
    change groupHomology.map _ _ n ≫ groupHomology.map _ _ n = groupHomology.map _ _ n
    rw [← groupHomology.map_comp]
    exact groupHomology.map_congr (by ext; rfl) (by apply DFunLike.ext; intro x; rfl) n
  have he := congrArg (fun f => f.hom.baseChange ℚ) hs
  simp only [ModuleCat.hom_comp, LinearMap.baseChange_comp] at he
  rw [← he]
  exact (rational_finiteIndex_homology_surjective (H.subgroupOf K) (Rep.res K.subtype A) n).comp
    (s.toLinearEquiv.baseChange ℤ ℚ _ _).surjective

end PolycyclicRecognition

end

end OAI
