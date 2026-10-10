import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

namespace OAI

/-! # Top homology as the kernel of the last differential -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] ModuleCat.isModule

def topHomologyKernelEquiv (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (h : C.d (n + 1) n = 0) :
    C.homology n ≃ₗ[ℤ] LinearMap.ker (C.d n (n - 1)).hom := by
  let e := (C.isoHomologyπ (n + 1) n (ChainComplex.prev ℕ n) h).symm ≪≫
    C.cyclesIsoSc' (n + 1) n (n - 1) (ChainComplex.prev ℕ n) (by cases n <;> simp) ≪≫
      (C.sc' (n + 1) n (n - 1)).moduleCatCyclesIso
  let a : C.homology n ≃+ LinearMap.ker (C.d n (n - 1)).hom := {
    toFun := e.hom
    invFun := e.inv
    left_inv := fun x => congrArg (fun f => f x) e.hom_inv_id
    right_inv := fun x => congrArg (fun f => f x) e.inv_hom_id
    map_add' := fun x y => map_add e.hom.hom x y }
  exact { a with map_smul' := fun r x => map_intCast_smul a ℤ ℤ r x }

end PolycyclicRecognition

end

end OAI
