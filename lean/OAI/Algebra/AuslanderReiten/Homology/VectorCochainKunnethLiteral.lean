import OAI.Algebra.AuslanderReiten.Homology.VectorCochainKunnethCycles
import OAI.Algebra.AuslanderReiten.Homology.CochainCycleClass
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.VectorCochain
universe u
variable (k : Type u) [Field k]
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]

private theorem totalZero_literalClass (U V : ℕ → ModuleCat.{u} k) (n : ℕ)
    (z : LinearMap.ker ((mapBifunctor (zeroDifferential k U) (zeroDifferential k V) F
      (.up ℕ)).d n (n+1)).hom) :
    (totalZeroHomologyIso k F U V n).hom.hom
      (literalClass k (mapBifunctor (zeroDifferential k U) (zeroDifferential k V) F (.up ℕ)) n z) = z.val := by
  have h := congrArg (fun f => f.hom ((literalCyclesIso k
    (mapBifunctor (zeroDifferential k U) (zeroDifferential k V) F (.up ℕ)) n).inv.hom z))
      (totalZeroHomologyIso_π k F U V n)
  exact h.trans (literalCyclesIso_inv_iCycles k _ n z)

variable (P Q : CochainComplex (ModuleCat.{u} k) ℕ)

theorem kunneth_literal_cycles (n : ℕ)
    (z : LinearMap.ker ((mapBifunctor (gradedCycles k P) (gradedCycles k Q) F (.up ℕ)).d n (n+1)).hom)
    (w : LinearMap.ker ((mapBifunctor P Q F (.up ℕ)).d n (n+1)).hom)
    (hw : ((mapBifunctorMap (cyclesInclusion k P) (cyclesInclusion k Q) F (.up ℕ)).f n).hom z.val = w.val) :
    (kunnethIso k F P Q n).hom.hom (literalClass k (mapBifunctor P Q F (.up ℕ)) n w) =
      ((mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) F (.up ℕ)).f n).hom z.val := by
  rw [← literalClass_map k _ n z w hw]
  have h := congrArg (fun f => f.hom
    (literalClass k (mapBifunctor (gradedCycles k P) (gradedCycles k Q) F (.up ℕ)) n z))
      (tensorCycles_kunneth k P F Q n)
  change _ = ((mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) F (.up ℕ)).f n).hom
    ((totalZeroHomologyIso k F (fun i => P.cycles i) (fun i => Q.cycles i) n).hom.hom
      (literalClass k (mapBifunctor (gradedCycles k P) (gradedCycles k Q) F (.up ℕ)) n z)) at h
  rw [totalZero_literalClass] at h
  exact h

local notation "T" => MonoidalCategory.curriedTensor (ModuleCat k)

theorem kunnethLinearEquiv_literal_tmul (i j n : ℕ) (hij : i+j=n)
    (x : LinearMap.ker (P.d i (i+1)).hom) (y : LinearMap.ker (Q.d j (j+1)).hom)
    (z : LinearMap.ker ((mapBifunctor P Q T (.up ℕ)).d n (n+1)).hom)
    (hz : z.val = (ιMapBifunctor P Q T (.up ℕ) i j n hij).hom (x.val ⊗ₜ[k] y.val)) :
    kunnethLinearEquiv k T P Q n (literalClass k (mapBifunctor P Q T (.up ℕ)) n z) =
      (DFinsupp.single ⟨(i,j), hij⟩ (literalClass k P i x ⊗ₜ[k] literalClass k Q j y) :
        Π₀ p : {p : ℕ × ℕ // p.1+p.2=n},
          (P.homology p.val.1 ⊗[k] Q.homology p.val.2)) := by
  let xc := (literalCyclesIso k P i).inv.hom x
  let yc := (literalCyclesIso k Q j).inv.hom y
  let t := (ιMapBifunctor (gradedCycles k P) (gradedCycles k Q) T (.up ℕ) i j n hij).hom
    (xc ⊗ₜ[k] yc)
  have ht : ((mapBifunctor (gradedCycles k P) (gradedCycles k Q) T (.up ℕ)).d n (n+1)).hom t = 0 := by
    rw [total_zero_differential]
    rfl
  let tc : LinearMap.ker ((mapBifunctor (gradedCycles k P) (gradedCycles k Q) T (.up ℕ)).d n (n+1)).hom := ⟨t, ht⟩
  have hm : ((mapBifunctorMap (cyclesInclusion k P) (cyclesInclusion k Q) T (.up ℕ)).f n).hom t = z.val := by
    have h := congrArg (fun f => f.hom (xc ⊗ₜ[k] yc))
      (ι_mapBifunctorMap (cyclesInclusion k P) (cyclesInclusion k Q) T (.up ℕ) i j n hij)
    change _ = (ιMapBifunctor P Q T (.up ℕ) i j n hij).hom
      ((P.iCycles i).hom xc ⊗ₜ[k] (Q.iCycles j).hom yc) at h
    rw [show (P.iCycles i).hom xc = x.val from literalCyclesIso_inv_iCycles k P i x,
      show (Q.iCycles j).hom yc = y.val from literalCyclesIso_inv_iCycles k Q j y] at h
    exact h.trans hz.symm
  change (ModuleCat.coprodIsoDirectSum _).hom.hom
    ((kunnethIso k T P Q n).hom.hom (literalClass k _ n z)) = _
  rw [kunneth_literal_cycles k T P Q n tc z hm]
  have hq := congrArg (fun f => f.hom (xc ⊗ₜ[k] yc))
    (ι_mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) T (.up ℕ) i j n hij)
  change _ = (ιMapBifunctor (gradedHomology k P) (gradedHomology k Q) T (.up ℕ) i j n hij).hom
    (literalClass k P i x ⊗ₜ[k] literalClass k Q j y) at hq
  change (ModuleCat.coprodIsoDirectSum _).hom.hom
    (((mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) T (.up ℕ)).f n).hom t) = _
  change ((mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) T (.up ℕ)).f n).hom t =
    (ιMapBifunctor (gradedHomology k P) (gradedHomology k Q) T (.up ℕ) i j n hij).hom
      (literalClass k P i x ⊗ₜ[k] literalClass k Q j y) at hq
  erw [hq]
  have hi := ModuleCat.ι_coprodIsoDirectSum_hom
    (fun p : {p : ℕ × ℕ // p.1+p.2=n} => ((T).obj (P.homology p.val.1)).obj (Q.homology p.val.2))
    ⟨(i,j), hij⟩
  exact congrArg (fun f => (ModuleCat.Hom.hom f)
    (literalClass k P i x ⊗ₜ[k] literalClass k Q j y)) hi

end ArExplicit.VectorCochain

end

end OAI
