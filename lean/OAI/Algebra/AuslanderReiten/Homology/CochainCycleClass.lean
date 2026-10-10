import OAI.Algebra.AuslanderReiten.HomComplex.HomCochainExtClass

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace ArExplicit.VectorCochain
universe u
variable (k : Type u) [Field k]
variable (P : CochainComplex (ModuleCat.{u} k) ℕ)

def literalCyclesIso (n : ℕ) :=
  P.cyclesIsoSc' (n-1) n (n+1) (by cases n <;> simp) (by simp) ≪≫
    (P.sc' (n-1) n (n+1)).moduleCatCyclesIso

def literalClass (n : ℕ) (x : LinearMap.ker (P.d n (n+1)).hom) : P.homology n :=
  (P.homologyπ n).hom ((literalCyclesIso k P n).inv.hom x)

@[simp] theorem literalCyclesIso_inv_iCycles (n : ℕ)
    (x : LinearMap.ker (P.d n (n+1)).hom) :
    (P.iCycles n).hom ((literalCyclesIso k P n).inv.hom x) = x.val := by
  have he : (literalCyclesIso k P n).inv ≫ P.iCycles n =
      ModuleCat.ofHom (LinearMap.ker (P.d n (n+1)).hom).subtype := by
    simp only [literalCyclesIso, Iso.trans_inv, Category.assoc,
      P.cyclesIsoSc'_inv_iCycles]
    exact (P.sc' (n-1) n (n+1)).moduleCatCyclesIso_inv_iCycles
  exact congrArg (fun f => f.hom x) he

theorem literalClass_eq_quotient (n : ℕ)
    (x : LinearMap.ker (P.d n (n+1)).hom) :
    literalClass k P n x =
      ((P.homologyIsoSc' (n-1) n (n+1) (by cases n <;> simp) (by simp)).inv).hom
        ((P.sc' (n-1) n (n+1)).moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk x)) := by
  have he : (literalCyclesIso k P n).inv ≫ P.homologyπ n =
      (P.sc' (n-1) n (n+1)).moduleCatLeftHomologyData.π ≫
        (P.sc' (n-1) n (n+1)).moduleCatHomologyIso.inv ≫
          (P.homologyIsoSc' (n-1) n (n+1) (by cases n <;> simp) (by simp)).inv := by
    simp only [literalCyclesIso, Iso.trans_inv, Category.assoc]
    rw [← P.π_homologyIsoSc'_inv (n-1) n (n+1) (by cases n <;> simp) (by simp),
      ← Category.assoc, ShortComplex.moduleCatCyclesIso_inv_π, Category.assoc]
  exact congrArg (fun f => f.hom x) he

variable {P} {Q : CochainComplex (ModuleCat.{u} k) ℕ}

theorem literalClass_map (f : P ⟶ Q) (n : ℕ)
    (x : LinearMap.ker (P.d n (n+1)).hom)
    (y : LinearMap.ker (Q.d n (n+1)).hom)
    (hxy : (f.f n).hom x.val = y.val) :
    (homologyMap f n).hom (literalClass k P n x) = literalClass k Q n y := by
  have hc : (cyclesMap f n).hom ((literalCyclesIso k P n).inv.hom x) =
      (literalCyclesIso k Q n).inv.hom y := by
    apply (ModuleCat.mono_iff_injective (Q.iCycles n)).mp inferInstance
    have hh := congrArg (fun u => u.hom ((literalCyclesIso k P n).inv.hom x))
      (cyclesMap_i f n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, literalCyclesIso_inv_iCycles] at hh ⊢
    exact hh.trans hxy
  have hh := congrArg (fun u => u.hom ((literalCyclesIso k P n).inv.hom x))
    (homologyπ_naturality f n)
  change (homologyMap f n).hom ((P.homologyπ n).hom _) = _
  rw [show (homologyMap f n).hom ((P.homologyπ n).hom ((literalCyclesIso k P n).inv.hom x)) =
    (Q.homologyπ n).hom ((cyclesMap f n).hom ((literalCyclesIso k P n).inv.hom x)) from hh]
  rw [hc]
  rfl

end ArExplicit.VectorCochain

end

end OAI
