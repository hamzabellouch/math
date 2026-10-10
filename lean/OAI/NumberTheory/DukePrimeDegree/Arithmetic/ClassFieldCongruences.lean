import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ClassFieldKernel
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ConductorModulus

namespace OAI

/-!
# Rational congruences give principal ray ideals

Only a finite modulus is needed for a totally real extension. An integer
divisible by the selected local prime powers imposes its higher-unit
conditions on every nonzero integral element congruent to one.
-/

noncomputable section
open scoped NumberField Classical

namespace DukePrimeDegree

open PrimeDegreePackets

variable {K : Type*} [Field K] [NumberField K]

theorem principal_local_mem_higherUnits
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {c : ℕ} (hc : 0 < c)
    (a : 𝓞 K) (ha : a ≠ 0)
    (hcong : algebraMap (𝓞 K) (v.adicCompletionIntegers K) a - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ c) :
    (IdeleGroup.principalIdele K
      (Units.mk0 (a : K) (by exact_mod_cast ha))).2 v ∈
        RayClass.localHigherUnitGroup v c := by
  let hu := completed_integral_isUnit_of_congruence v hc hcong
  let z : (v.adicCompletionIntegers K)ˣ := hu.unit
  let y : (v.adicCompletionIntegers K).units :=
    (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm z
  apply (RayClass.mem_localHigherUnitGroup_iff v c _).mpr
  refine ⟨y, ?_, ?_⟩
  · apply Units.ext
    change ((z : v.adicCompletionIntegers K) : v.adicCompletion K) =
      ((a : K) : v.adicCompletion K)
    rw [show (z : v.adicCompletionIntegers K) =
        algebraMap (𝓞 K) (v.adicCompletionIntegers K) a from hu.unit_spec]
    rfl
  · apply (RayClass.localHigherUnitMap_eq_one_iff v c y).mpr
    change (z : v.adicCompletionIntegers K) - 1 ∈ _
    rwa [show (z : v.adicCompletionIntegers K) =
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) a from hu.unit_spec]

theorem principalIdele_mem_even_ray_of_congruence
    (m : RayClass.Modulus K) (hm : m.infinitePart = ∅)
    (N : ℕ)
    (hN : ∀ v ∈ m.finitePart.support,
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) (N : 𝓞 K) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m.finitePart v)
    (a : 𝓞 K) (ha : a ≠ 0)
    (hcong : a - 1 ∈ ThetaConstruction.rationalModulusIdeal (𝓞 K) N) :
    IdeleGroup.principalIdele K (Units.mk0 (a : K) (by exact_mod_cast ha)) ∈
      RayClass.idelePrimeToModulusSubgroup m := by
  constructor
  · change (IdeleGroup.principalIdele K
      (Units.mk0 (a : K) (by exact_mod_cast ha))).1 ∈ m.infiniteCongruenceSubgroup
    rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
    intro v hv
    simp only [hm, Finset.notMem_empty] at hv
  · intro v hv
    apply principal_local_mem_higherUnits v
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)) a ha
    exact completed_congruence_of_integer v (m.finitePart v) N (hN v hv) hcong

end DukePrimeDegree

end

end OAI
