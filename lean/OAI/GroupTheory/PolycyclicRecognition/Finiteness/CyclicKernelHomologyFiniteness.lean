import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RankOneKernelFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CyclicTopHomologyInjection

namespace OAI

/-! # Finiteness descends through a nonzero cyclic top-degree kernel -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2

theorem cyclic_topHomology_finiteness {G : Type} [Group G]
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (P : ProjectiveResolution (trivialIntegral q.ker)) (A : Rep ℤ G) (d : ℕ)
    (hvanish : IsZero (groupHomology (Rep.res q.ker.subtype A) (d + 1)))
    (htorsion : ∀ (z : ℤ) (x : groupHomology (Rep.res q.ker.subtype A) d),
      z • x = 0 → z = 0 ∨ x = 0)
    (hcomm : ∀ x y : groupHomology (Rep.res q.ker.subtype A) d,
      x ≠ 0 → y ≠ 0 → ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y)
    [Module.Finite ℤ (groupHomology A (d + 1))]
    (x : groupHomology A (d + 1)) (hx : x ≠ 0) :
    Module.Finite ℤ (groupHomology (Rep.res q.ker.subtype A) d) := by
  let := integerQuotient_isCyclic q t ht
  let := integerQuotient_infinite q t ht
  let M : ModuleCat ℤ := ((quotientInducedResolution q.ker P).complex.coinvariantsTensorObj A).homology d
  let E : M ≅ groupHomology (Rep.res q.ker.subtype A) d :=
    inducedResolutionHomologyIso q.ker A P d
  have hEinj : Function.Injective E.hom :=
    (ModuleCat.mono_iff_injective E.hom).mp inferInstance
  obtain ⟨htor, hcom⟩ := integralRankOne_properties_of_injective E.hom hEinj htorsion hcomm
  let f : M ⟶ M := HomologicalComplex.homologyMap (integerExtensionTensorMap q t P A) d
  have hfinite : Module.Finite ℤ M := rankOne_module_finite_of_nonzero_kernel htor hcom f
    (integerExtensionHomologyKernelIso q t ht P A d hvanish) x hx
  let := hfinite
  exact Module.Finite.equiv E.toLinearEquiv

end PolycyclicRecognition

end

end OAI
