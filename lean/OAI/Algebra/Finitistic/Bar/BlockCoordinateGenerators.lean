import OAI.Algebra.Finitistic.Bar.IndexedMultibarTotal

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
universe u
section Congr
variable {D : Type u} [Ring D]
variable {I : Type} [DecidableEq I] (V W : I → ModuleCat.{u} D)
  (e : ∀ i, V i ≅ W i)

theorem congrLinearEquiv_symm_lof (i : I) (v : W i) :
    (DirectSum.congrLinearEquiv (fun i => (e i).toLinearEquiv)).symm
      (DirectSum.lof D I (fun i => W i) i v) =
    DirectSum.lof D I (fun i => V i) i ((e i).inv.hom v) := by
  change DirectSum.lmap (fun i => (e i).toLinearEquiv.symm.toLinearMap)
    (DirectSum.lof D I (fun i => W i) i v) = _
  rw [DirectSum.lmap_lof]
  rfl
end Congr

variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (N : ModuleCat.{u} D) : Module k N := BimoduleTensor.scalarModule k D N
local instance (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "Z" => (Functor.obj (ChainComplex.single₀ (ModuleCat D)) N)
local instance (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _
local instance (r n : ℕ) : DecidableEq (Multibar.Indexed.Shape r n) := Classical.decEq _

/-- The inverse coordinate map on a literal block generator is exactly its
recursive tensor inclusion, with the proved tensor-coordinate isomorphism. -/
theorem moduleFlatCoordinates_inv_lof (r n : ℕ) (p : Multibar.Indexed.Shape (r+n) r) :
    ModuleCat.ofHom (DirectSum.lof D (Multibar.Indexed.Shape (r+n) r)
      (Multibar.Indexed.outerTensor k D X N) p) ≫ (moduleFlatCoordinates k D X N r n).inv =
    (reindexedModuleSummandIso k D X N r n p).inv ≫
      lof (leadingBarSequence k D X r) Z (r+1) n ((moduleShapeEquiv r n).symm p).val := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  dsimp only [moduleFlatCoordinates]
  erw [Iso.trans_inv, Iso.trans_inv]
  simp only [ModuleCat.hom_comp,
    LinearEquiv.toModuleIso_inv, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  erw [congrLinearEquiv_symm_lof, DirectSum.lequivCongrLeft_symm_lof]
  simp only [supportIso]
  exact DirectSum.toModule_lof D
    (N := flat (leadingBarSequence k D X r) Z (r+1) n)
    (M := fun t : {t : Index (r+1) n // inputDegree (r+1) t=0} =>
      summand (leadingBarSequence k D X r) Z (r+1) n t.val)
    ((moduleShapeEquiv r n).symm p) ((reindexedModuleSummandIso k D X N r n p).inv.hom v)

/-- The same inverse map into the actual leading total; this is the concrete
map to use when comparing the literal parity faces with the recursive total. -/
theorem leadingModuleCoordinates_inv_lof (r n : ℕ) (p : Multibar.Indexed.Shape (r+n) r) :
    ModuleCat.ofHom (DirectSum.lof D (Multibar.Indexed.Shape (r+n) r)
      (Multibar.Indexed.outerTensor k D X N) p) ≫ (moduleFlatCoordinates k D X N r n).inv ≫
      assemble (leadingBarSequence k D X r) Z (r+1) n =
    (reindexedModuleSummandIso k D X N r n p).inv ≫
      inclusion (leadingBarSequence k D X r) Z (r+1) n ((moduleShapeEquiv r n).symm p).val := by
  erw [← Category.assoc, moduleFlatCoordinates_inv_lof, Category.assoc, lof_assemble]

/-- Full horizontal-plus-signed-vertical formula on each actual Shape summand.
The index is obtained by the proved inverse parsing, not an assumed correspondence. -/
theorem indexedDifferential_on_block (r n : ℕ)
    (p : Multibar.Indexed.Shape (r+(n+1)) r) :
    let t := ((moduleShapeEquiv r (n+1)).symm p).val
    ModuleCat.ofHom (DirectSum.lof D (Multibar.Indexed.Shape (r+(n+1)) r)
      (Multibar.Indexed.outerTensor k D X N) p) ≫ indexedDifferential k D X N r n =
    (reindexedModuleSummandIso k D X N r (n+1) p).inv ≫
      (horizontal (leadingBarSequence k D X r) Z r n t.1.val.1 t.1.val.2 t.1.property t.2 +
       vertical (leadingBarSequence k D X r) Z r n t.1.val.1 t.1.val.2 t.1.property t.2
         (differential (leadingBarSequence k D X r) Z r)) ≫
      (moduleFlatCoordinates k D X N r n).hom := by
  dsimp only
  erw [indexedDifferential, ← Category.assoc, moduleFlatCoordinates_inv_lof, Category.assoc]
  simp only [flatLeadingMultibar, flatComplex, ChainComplex.of_d]
  congr 1
  let t := ((moduleShapeEquiv r (n+1)).symm p).val
  exact lof_differential_succ_assoc (leadingBarSequence k D X r) Z r n
    t.1.val.1 t.1.val.2 t.1.property t.2 (moduleFlatCoordinates k D X N r n).hom
end DerivedBar.RecursiveTotal

end

end OAI
