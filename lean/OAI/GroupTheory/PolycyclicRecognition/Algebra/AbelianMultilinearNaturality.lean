import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianMultilinearHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianSecondHomologyNaturality

namespace OAI

/-! # Naturality of multilinear evaluation on abelian group homology -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A B V W : Type} [CommGroup A] [CommGroup B]
  [AddCommGroup V] [AddCommGroup W]

theorem abelianMultilinearChains_natural {n : ℕ} (f : A →* B)
    (F : MultilinearMap ℤ (fun _ : Fin n => Additive A) V)
    (H : MultilinearMap ℤ (fun _ : Fin n => Additive B) W)
    (L : V →ₗ[ℤ] W)
    (h : ∀ v : Fin n → A, L (F (Additive.ofMul ∘ v)) =
      H (Additive.ofMul ∘ (f ∘ v))) :
    (abelianMultilinearChains H).comp
      ((groupHomology.chainsMap f (integralTrivialCoefficientMap f)).f n).hom =
      L.comp (abelianMultilinearChains F) := by
  apply Finsupp.lhom_ext'
  intro v
  apply LinearMap.ext
  intro z
  change abelianMultilinearChains H
      ((groupHomology.chainsMap f (integralTrivialCoefficientMap f)).f n
        (Finsupp.single v z)) = L (abelianMultilinearChains F (Finsupp.single v z))
  rw [groupHomology.chainsMap_f_single]
  change abelianMultilinearChains H (Finsupp.single (f ∘ v) z) = _
  rw [abelianMultilinearChains_single, abelianMultilinearChains_single, map_smul, h]

theorem abelianMultilinearHomology_natural {n : ℕ} (f : A →* B)
    (F : MultilinearMap ℤ (fun _ : Fin n => Additive A) V)
    (H : MultilinearMap ℤ (fun _ : Fin n => Additive B) W)
    (L : V →ₗ[ℤ] W)
    (h : ∀ v : Fin n → A, L (F (Additive.ofMul ∘ v)) =
      H (Additive.ofMul ∘ (f ∘ v)))
    (z : groupHomology (integralTrivialCoefficient A) n) :
    abelianMultilinearHomology H
        (groupHomology.map f (integralTrivialCoefficientMap f) n z) =
      L (abelianMultilinearHomology F z) := by
  induction z using groupHomology_induction_on with
  | h z =>
    have hp := congrArg (fun E => E.hom z)
      (groupHomology.π_map f (integralTrivialCoefficientMap f) n)
    change groupHomology.map f (integralTrivialCoefficientMap f) n
        (groupHomology.π (integralTrivialCoefficient A) n z) =
      groupHomology.π (integralTrivialCoefficient B) n
        (groupHomology.cyclesMap f (integralTrivialCoefficientMap f) n z) at hp
    rw [hp, abelianMultilinearHomology_π, abelianMultilinearHomology_π]
    have hc := congrArg (fun E => E.hom z)
      (HomologicalComplex.cyclesMap_i
        (groupHomology.chainsMap f (integralTrivialCoefficientMap f)) n)
    change groupHomology.iCycles (integralTrivialCoefficient B) n
        (groupHomology.cyclesMap f (integralTrivialCoefficientMap f) n z) =
      (groupHomology.chainsMap f (integralTrivialCoefficientMap f)).f n
        (groupHomology.iCycles (integralTrivialCoefficient A) n z) at hc
    rw [hc]
    exact LinearMap.congr_fun (abelianMultilinearChains_natural f F H L h)
      (groupHomology.iCycles (integralTrivialCoefficient A) n z)

end PolycyclicRecognition

end

end OAI
