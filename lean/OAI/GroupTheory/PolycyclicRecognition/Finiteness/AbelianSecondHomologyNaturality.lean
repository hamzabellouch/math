import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianSecondHomologyPairing
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

namespace OAI

/-! # Naturality of the bilinear second-homology pairing -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A B M P : Type} [CommGroup A] [CommGroup B] [AddCommGroup M] [AddCommGroup P]

def integralTrivialCoefficientMap (f : A →* B) :
    integralTrivialCoefficient A ⟶ Rep.res f (integralTrivialCoefficient B) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

theorem bilinearPairingChains_natural (f : A →* B)
    (b : Additive A →+ Additive A →+ M) (c : Additive B →+ Additive B →+ P)
    (L : M →ₗ[ℤ] P)
    (h : ∀ a d, L (b (Additive.ofMul a) (Additive.ofMul d)) =
      c (Additive.ofMul (f a)) (Additive.ofMul (f d))) :
    (bilinearPairingChains c).comp
      (groupHomology.chainsMap₂ f (integralTrivialCoefficientMap f)).hom =
      L.comp (bilinearPairingChains b) := by
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext
  intro z
  rcases p with ⟨a, d⟩
  simp [groupHomology.chainsMap₂, integralTrivialCoefficientMap,
    bilinearPairingChains_single, h]

theorem bilinearPairingHomology_natural (f : A →* B)
    (b : Additive A →+ Additive A →+ M) (c : Additive B →+ Additive B →+ P)
    (L : M →ₗ[ℤ] P)
    (h : ∀ a d, L (b (Additive.ofMul a) (Additive.ofMul d)) =
      c (Additive.ofMul (f a)) (Additive.ofMul (f d)))
    (z : groupHomology.H2 (integralTrivialCoefficient A)) :
    bilinearPairingHomology c (groupHomology.map f (integralTrivialCoefficientMap f) 2 z) =
      L (bilinearPairingHomology b z) := by
  induction z using groupHomology.H2_induction_on with
  | h z =>
    have hn := congrArg (fun F => F.hom z)
      (groupHomology.H2π_comp_map f (integralTrivialCoefficientMap f))
    change groupHomology.map f (integralTrivialCoefficientMap f) 2
      (groupHomology.H2π (integralTrivialCoefficient A) z) =
        groupHomology.H2π (integralTrivialCoefficient B)
          (groupHomology.mapCycles₂ f (integralTrivialCoefficientMap f) z) at hn
    rw [hn, bilinearPairingHomology_π, bilinearPairingHomology_π,
      groupHomology.coe_mapCycles₂]
    exact LinearMap.congr_fun (bilinearPairingChains_natural f b c L h) z.val

end PolycyclicRecognition

end

end OAI
