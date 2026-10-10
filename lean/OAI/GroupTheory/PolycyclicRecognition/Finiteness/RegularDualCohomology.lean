import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularPairingNaturality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CohomologicalFiniteness
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

namespace OAI

/-! # The underlying module of the top regular-dual cokernel -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def regularDualCokernelCohomologyIso
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ)
    (hbound : IsZero (P.complex.X (n + 1))) :
    (forget₂ (Rep ℤ G) (ModuleCat ℤ)).obj
        (cokernel (regularDualMap (P.complex.d n (n - 1)))) ≅
      groupCohomology (Rep.leftRegular ℤ G) n := by
  classical
  let C := P.complex.linearYonedaObj ℤ (Rep.leftRegular ℤ G)
  let F := forget₂ (Rep ℤ G) (ModuleCat ℤ)
  have hz : C.d n (n + 1) = 0 := by
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro q
    change P.complex.X n ⟶ Rep.leftRegular ℤ G at q
    change P.complex.d (n + 1) n ≫ q = 0
    rw [hbound.eq_of_src (P.complex.d (n + 1) n) 0, zero_comp]
  have hd : C.d (n - 1) n = F.map (regularDualMap (P.complex.d n (n - 1))) := by
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro q
    rfl
  let e : C.homology n ≅ cokernel (C.d (n - 1) n) :=
    (C.isoHomologyι n (n + 1) (CochainComplex.next ℕ n) hz).trans
      ((C.opcyclesIsoSc' (n - 1) n (n + 1) (by cases n <;> simp) (CochainComplex.next ℕ n)).trans
        (C.sc' (n - 1) n (n + 1)).opcyclesIsoCokernel)
  exact (PreservesCokernel.iso F (regularDualMap (P.complex.d n (n - 1)))).trans
    ((cokernelIsoOfEq hd).symm.trans
      (e.symm.trans (groupCohomologyIso (Rep.leftRegular ℤ G) n P).symm))

end PolycyclicRecognition

end

end OAI
