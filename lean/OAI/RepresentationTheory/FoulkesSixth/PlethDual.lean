import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.SymOperations

namespace OAI

noncomputable section

namespace Foulkes.PlethDual
universe u
open Module SymmetricTensor
variable (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

local instance plethDualSymAddCommGroup (degree : ℕ) (space : Type u)
    [AddCommGroup space] [Module ℂ space] : AddCommGroup (Sym degree space) :=
  (Sym degree space).addCommGroup

def equiv : Sym a (Sym b (Dual ℂ V)) ≃ₗ[ℂ] Dual ℂ (Sym a (Sym b V)) :=
  (symEquiv a (dualEquiv b (V := V))).trans (dualEquiv a (V := Sym b V))

def flipEquiv : Sym a (Sym b V) ≃ₗ[ℂ] Dual ℂ (Sym a (Sym b (Dual ℂ V))) :=
  (Module.evalEquiv ℂ (Sym a (Sym b V))).trans (equiv a b V).dualMap

@[simp] lemma flipEquiv_apply (x : Sym a (Sym b V)) (d : Sym a (Sym b (Dual ℂ V))) :
    flipEquiv a b V x d = equiv a b V d x := rfl

@[simp] lemma equiv_apply (d : Sym a (Sym b (Dual ℂ V))) (x : Sym a (Sym b V)) :
    equiv a b V d x = pairing a (symMap a (dualEquiv b (V := V)).toLinearMap d) x := rfl

lemma natural (g : V →ₗ[ℂ] V) (d : Sym a (Sym b (Dual ℂ V))) (x : Sym a (Sym b V)) :
    equiv a b V (symMap a (symMap b g.dualMap) d) x =
      equiv a b V d (symMap a (symMap b g) x) := by
  have hi : (dualEquiv b (V := V)).toLinearMap.comp (symMap b g.dualMap) =
      (symMap b g).dualMap.comp (dualEquiv b (V := V)).toLinearMap := by
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro v
    exact pairing_map b g q v
  have hs : symMap a (dualEquiv b (V := V)).toLinearMap
      (symMap a (V := Sym b (Dual ℂ V)) (W := Sym b (Dual ℂ V)) (symMap b g.dualMap) d) =
      symMap a (symMap b g).dualMap (symMap a (dualEquiv b (V := V)).toLinearMap d) := by
    change ((symMap a (dualEquiv b (V := V)).toLinearMap).comp
      (symMap a (symMap b g.dualMap))) d =
      ((symMap a (symMap b g).dualMap).comp
        (symMap a (dualEquiv b (V := V)).toLinearMap)) d
    rw [← symMap_comp, hi, symMap_comp]
  simp only [equiv_apply, hs]
  exact pairing_map a (symMap b g) _ x

end Foulkes.PlethDual

end

end OAI
