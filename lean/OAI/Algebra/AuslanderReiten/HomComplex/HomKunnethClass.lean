import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHomKunneth
import OAI.Algebra.AuslanderReiten.HomComplex.HomCochainNativeClass
import OAI.Algebra.AuslanderReiten.Homology.VectorCochainKunnethLiteral

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]
variable (i j n : ℕ) (h : i+j=n)
variable (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V)
variable (hf : f.comp (P.d (i+1) i).hom=0) (hg : g.comp (Q.d (j+1) j).hom=0)
include hf hg

theorem elementary_closed :
    (elementaryHom k A B P Q U V i j n h f g).comp ((complex k A B P Q).d (n+1) n).hom=0 := by
  rw [elementary_d, hf, hg]
  simp [elementaryHom]
  change (0 : (complex k A B P Q).X (n+1) →ₗ[A ⊗[k] B] moduleObject k A B U V) +
    ((-1 : ℤˣ)^i) • 0 = 0
  simp only [smul_zero, add_zero]

omit [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
    [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)] in
theorem elementary_total_closed :
    ((homCochainTotal k A B P Q U V).d n (n+1)).hom
      ((homCochainInclusion k A B P Q U V i j n h).hom (f ⊗ₜ[k] g))=0 := by
  rw [homCochainInclusion_d_tmul, hf, hg]
  simp

theorem homKunnethEquiv_elementary
    (xf : LinearMap.ker ((homCochain k A P U).d i (i+1)).hom)
    (xg : LinearMap.ker ((homCochain k B Q V).d j (j+1)).hom)
    (hx : xf.val=f) (hy : xg.val=g)
    (z : LinearMap.ker ((homCochain k (A ⊗[k] B) (complex k A B P Q)
      (moduleObject k A B U V)).d n (n+1)).hom)
    (hz : z.val=elementaryHom k A B P Q U V i j n h f g) :
    homKunnethEquiv k A B P Q U V n
      (VectorCochain.literalClass k _ n z) =
      (DFinsupp.single ⟨(i,j),h⟩
        (VectorCochain.literalClass k (homCochain k A P U) i xf ⊗ₜ[k]
          VectorCochain.literalClass k (homCochain k B Q V) j xg) :
        Π₀ p : Diagonal n, (homCochain k A P U).homology p.val.1 ⊗[k]
          (homCochain k B Q V).homology p.val.2) := by
  let w : LinearMap.ker ((homCochainTotal k A B P Q U V).d n (n+1)).hom :=
    ⟨(homCochainInclusion k A B P Q U V i j n h).hom (f ⊗ₜ[k] g),
      elementary_total_closed k A B P Q U V i j n h f g hf hg⟩
  let e := (homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).mapIso
    (homCochainTotalIso k A B P Q U V)
  have hmap := VectorCochain.literalClass_map k (homCochainTotalIso k A B P Q U V).hom n w z
    (by exact hz.symm)
  have hcancel : e.inv.hom (VectorCochain.literalClass k _ n z) =
      VectorCochain.literalClass k _ n w := by
    rw [← hmap]
    exact e.toLinearEquiv.symm_apply_apply _
  change VectorCochain.kunnethLinearEquiv k (MonoidalCategory.curriedTensor (ModuleCat.{u} k))
    (homCochain k A P U) (homCochain k B Q V) n
      (e.inv.hom (VectorCochain.literalClass k _ n z)) = _
  rw [hcancel]
  apply VectorCochain.kunnethLinearEquiv_literal_tmul k _ _ i j n h xf xg w
  change (homCochainInclusion k A B P Q U V i j n h).hom (f ⊗ₜ[k] g) =
    (homCochainInclusion k A B P Q U V i j n h).hom (xf.val ⊗ₜ[k] xg.val)
  rw [hx, hy]

end ArExplicit.ExternalTensor

end

end OAI
