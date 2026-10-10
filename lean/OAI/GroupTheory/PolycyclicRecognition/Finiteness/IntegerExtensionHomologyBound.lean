import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerExtensionHomology

namespace OAI

/-! # A homology dimension bound through an infinite cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G]

theorem homology_bound_of_integer_quotient
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (d : ℕ)
    (hN : ∀ B : Rep ℤ q.ker, ∀ i, d < i → IsZero (groupHomology B i)) :
    ∀ A : Rep ℤ G, ∀ i, d + 1 < i → IsZero (groupHomology A i) := by
  classical
  let := integerQuotient_isCyclic q t ht
  let := integerQuotient_infinite q t ht
  intro A i hi
  cases i with
  | zero => omega
  | succ i =>
    let P := Rep.standardResolution ℤ q.ker
    let f := HomologicalComplex.homologyMap (integerExtensionTensorMap q t P A) i
    have hsource : IsZero
        (((quotientInducedResolution q.ker P).complex.coinvariantsTensorObj A).homology i) :=
      IsZero.of_iso (hN (Rep.res q.ker.subtype A) i (by omega))
        (inducedResolutionHomologyIso q.ker A P i)
    have hk : IsZero (kernel f) := IsZero.of_mono (kernel.ι f) hsource
    exact IsZero.of_iso hk (integerExtensionHomologyKernelIso q t ht P A i
      (hN (Rep.res q.ker.subtype A) (i + 1) (by omega)))

end PolycyclicRecognition

end

end OAI
