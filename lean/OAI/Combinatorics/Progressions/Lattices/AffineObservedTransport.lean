import OAI.Combinatorics.Progressions.Lattices.AffineSampleAlphabet

namespace OAI

section

namespace Erdos3

open scoped Classical

variable {ι J I Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype I] [Fintype Ω]
  (q : ι → ℕ) [∀ i, NeZero (q i)] (p : FiniteProbabilityWeights Ω)
  (F : Ω → Option J × I → ℤ) (w : Ω → ℝ)

noncomputable def affinePrimeObservedDensity : (∀ i, (J → I → ZMod (q i)) × (I → ZMod (q i))) → ℝ :=
  observedProductDensity (fun i => residueAffineSource (J := J) (G := I → ZMod (q i)))
    p (fun z => affinePrimeCoordinateObservation q (F z)) w

theorem affinePrimeObservedDensity_pullback (x : ∀ i, Option J × I → ZMod (q i)) :
    affinePrimeObservedDensity q p F w (fun i => affineSampleAlphabetEquiv (x i)) =
      observedProductDensity (primeCoordinateReference (σ := Option J × I) q)
        p (fun z => primeCoordinateObservation q (F z)) w x :=
  observedProductDensity_coordinate_equiv _ _ (fun _ => affineSampleAlphabetEquiv)
    (fun _ => affineSampleAlphabet_weight) p (fun z => primeCoordinateObservation q (F z)) w x

theorem affinePrimeObservedDensity_energy (D : Finset (Finset ι)) :
    productANOVAEnergy (primeCoordinateReference (σ := Option J × I) q) D
      (observedProductDensity (primeCoordinateReference (σ := Option J × I) q)
        p (fun z => primeCoordinateObservation q (F z)) w) =
      productANOVAEnergy (fun i => residueAffineSource (J := J) (G := I → ZMod (q i))) D
        (affinePrimeObservedDensity q p F w) :=
  observedProductDensity_coordinate_energy _ _ (fun _ => affineSampleAlphabetEquiv)
    (fun _ => affineSampleAlphabet_weight) p (fun z => primeCoordinateObservation q (F z)) w D

theorem affinePrimeObservedDensity_marginals_iff (η : ℝ) (r : ℕ) :
    ProductMarginalsClose (fun i => residueAffineSource (J := J) (G := I → ZMod (q i)))
      (affinePrimeObservedDensity q p F w) η r ↔
      ProductMarginalsClose (primeCoordinateReference (σ := Option J × I) q)
        (observedProductDensity (primeCoordinateReference (σ := Option J × I) q)
          p (fun z => primeCoordinateObservation q (F z)) w) η r := by
  rw [productMarginalsClose_coordinate_equiv_iff
    (primeCoordinateReference (σ := Option J × I) q)
    (fun i => residueAffineSource (J := J) (G := I → ZMod (q i)))
    (fun _ => affineSampleAlphabetEquiv) (fun _ => affineSampleAlphabet_weight)]
  simp only [affinePrimeObservedDensity_pullback]

theorem affinePrimeObservedDensity_section (T A : Finset ι)
    (z x : ∀ i, Option J × I → ZMod (q i)) :
    productSectionAverage (primeCoordinateReference (σ := Option J × I) q) T A z
      (observedProductDensity (primeCoordinateReference (σ := Option J × I) q)
        p (fun v => primeCoordinateObservation q (F v)) w) x =
      productSectionAverage (fun i => residueAffineSource (J := J) (G := I → ZMod (q i))) T A
        (fun i => affineSampleAlphabetEquiv (z i)) (affinePrimeObservedDensity q p F w)
        (fun i => affineSampleAlphabetEquiv (x i)) := by
  have he := funext (affinePrimeObservedDensity_pullback q p F w)
  rw [← he]
  exact productSectionAverage_coordinate_transport _ _ (fun _ => affineSampleAlphabetEquiv)
    (fun _ => affineSampleAlphabet_mean) T A z _ x

theorem affinePrimeObservedDensity_section_energy (T A : Finset ι)
    (z : ∀ i, Option J × I → ZMod (q i)) (D : Finset (Finset ι)) :
    productANOVAEnergy (primeCoordinateReference (σ := Option J × I) q) D
      (productSectionAverage (primeCoordinateReference (σ := Option J × I) q) T A z
        (observedProductDensity (primeCoordinateReference (σ := Option J × I) q)
          p (fun v => primeCoordinateObservation q (F v)) w)) =
      productANOVAEnergy (fun i => residueAffineSource (J := J) (G := I → ZMod (q i))) D
        (productSectionAverage (fun i => residueAffineSource (J := J) (G := I → ZMod (q i))) T A
          (fun i => affineSampleAlphabetEquiv (z i)) (affinePrimeObservedDensity q p F w)) := by
  rw [show productSectionAverage (primeCoordinateReference (σ := Option J × I) q) T A z
      (observedProductDensity (primeCoordinateReference (σ := Option J × I) q)
        p (fun v => primeCoordinateObservation q (F v)) w) = _ from
    funext (affinePrimeObservedDensity_section q p F w T A z)]
  exact productANOVAEnergy_coordinate_transport _ _ (fun _ => affineSampleAlphabetEquiv)
    (fun _ => affineSampleAlphabet_mean) D _

end Erdos3

end

end OAI
