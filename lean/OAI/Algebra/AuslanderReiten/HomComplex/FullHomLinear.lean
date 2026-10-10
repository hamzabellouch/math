import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProducts
import Mathlib.Algebra.Homology.Linear

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit.CompleteComparison

universe u v

section Cochains

variable (k : Type u) [CommRing k]
variable {C : Type*} [Category* C] [Preadditive C] [Linear k C]
variable (K L : CochainComplex C ℤ) (n : ℤ)

def fullHomCoboundaries : Submodule k (Cocycle K L n) where
  __ := coboundaries K L n
  smul_mem' a x hx := by
    obtain ⟨m, hm, y, hy⟩ := hx
    refine ⟨m, hm, a • y, ?_⟩
    rw [δ_smul, hy]
    rfl

instance fullHomModule : Module k (CohomologyClass K L n) :=
  inferInstanceAs (Module k ((Cocycle K L n) ⧸ fullHomCoboundaries k K L n))

variable {K L n}

@[simp]
theorem fullHom_mk_smul (a : k) (x : Cocycle K L n) :
    CohomologyClass.mk (a • x) = a • CohomologyClass.mk x := rfl

theorem cocycleHom_smul (a : k) (x : Cocycle K L n) :
    Cocycle.equivHomShift.symm (a • x) = a • Cocycle.equivHomShift.symm x := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [cocycleHom_component, HomologicalComplex.smul_f_apply,
    Cocycle.coe_smul, Cochain.smul_v]

end Cochains

variable {k R : Type u} [CommRing k] [Ring R] [Algebra k R]
open scoped ModuleCat.Algebra

variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

theorem cokernelMap_smul (a : k) (F : P ⟶ Q) (n : ℤ) :
    cokernelMap (a • F) n = a • cokernelMap F n := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) z
  change (LinearMap.range (Q.d (n + 1) n).hom).mkQ (a • (F.f n).hom x) =
    a • (LinearMap.range (Q.d (n + 1) n).hom).mkQ ((F.f n).hom x)
  exact ((LinearMap.range (Q.d (n + 1) n).hom).mkQ.restrictScalars k).map_smul a _

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ}

theorem cocycleComparisonMap_smul (a : k) (x : Cocycle K L n) :
    cocycleComparisonMap (a • x) = a • cocycleComparisonMap x := by
  unfold cocycleComparisonMap
  rw [cocycleHom_smul]
  apply HomologicalComplex.Hom.ext
  funext i
  have hi : negIndexEmbedding.f (-i) = i := neg_neg i
  simp only [HomologicalComplex.extendMap_f _ _ hi,
    HomologicalComplex.smul_f_apply, Linear.comp_smul, Linear.smul_comp]

theorem fullHomStableEquiv_smul (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain (L⟦n⟧)))
    (a : k) (x : CohomologyClass K L n) :
    fullHomStableEquiv K L n hK hL (a • x) = a • fullHomStableEquiv K L n hK hL x := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [← fullHom_mk_smul, fullHomStableEquiv_mk, fullHomStableEquiv_mk,
    cocycleComparisonMap_smul, cokernelMap_smul, StableHom.classOf_smul]

noncomputable def fullHomStableLinearEquiv
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain (L⟦n⟧))) :
    CohomologyClass K L n ≃ₗ[k]
      StableHom R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain (L⟦n⟧)) 0) :=
  { fullHomStableEquiv K L n hK hL with
    map_smul' := fullHomStableEquiv_smul hK hL }

end ArExplicit.CompleteComparison

end OAI
