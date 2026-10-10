import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.ArithmeticIdealArtin
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness

namespace OAI

/-!
# The even Artin kernel for totally real extensions

The ordinary finite congruence modulus needed by even Hecke characters is
obtained from the actual class-field conductor, whose infinite part is
empty in a totally real extension.
-/

open scoped NumberField

noncomputable section

namespace DukePrimeDegree

open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
  GlobalClassFieldTheory.IdealClassFieldTheory

/-- The norm subgroup of a totally real abelian extension has a defining
modulus with no infinite places. -/
theorem exists_even_artin_modulus
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] [NumberField.IsTotallyReal L] :
    ∃ m : RayClass.Modulus K, m.infinitePart = ∅ ∧
      m.congruenceSubgroup ≤ (ideleClassNorm K L).range := by
  classical
  let H := ideleClassNormConductorialSubgroup (K := K) (L := L)
  refine ⟨H.fullConductor, ?_, H.fullConductor_isDefiningModulus⟩
  change (ideleClassNormConductorialSubgroup (K := K) (L := L)).fullConductor.infinitePart = ∅
  rw [ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus]
  apply Finset.filter_eq_empty_iff.mpr
  intro v _ hv
  apply hv
  intro w _
  exact (NumberField.IsTotallyReal.isReal w).isUnramified K

/-- Arithmetic normalization of the Artin map still annihilates every
principal ray ideal. -/
theorem arithmetic_artin_eq_one_of_principal_ray
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (m : RayClass.Modulus K)
    (hm : m.congruenceSubgroup ≤ (ideleClassNorm K L).range)
    (I : RayClass.primeToModulusIdeals m)
    (hI : I ∈ RayClass.principalRayIdealSubgroup m) :
    arithmeticIdealArtinGaloisMap (K := K) (L := L) m hm I = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [arithmeticIdealArtinGaloisMap_ker]
  exact principalRayIdealSubgroup_le_idealArtinKernel m
    (ideleClassNorm K L).range hm hI

end DukePrimeDegree

end

end OAI
