import OAI.Analysis.IrrationalRotation.Model.ProductCoupling
import OAI.Analysis.IrrationalRotation.Model.PrefixDomination

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

abbrev PrefixIndex (D : ℕ) := ↥(Finset.range D)
abbrev TailIndex (D : ℕ) := {i : ℕ // i ∉ Finset.range D}
abbrev PrefixPairs (D : ℕ) := PrefixIndex D → ℝ × ℝ
abbrev TailValues (D : ℕ) := TailIndex D → ℝ

def assemblePrefixPair (D : ℕ) (z : PrefixPairs D × TailValues D) : Endpoint × Endpoint :=
  ((fun i => if hi : i ∈ Finset.range D then (z.1 ⟨i, hi⟩).1 else z.2 ⟨i, hi⟩),
   (fun i => if hi : i ∈ Finset.range D then (z.1 ⟨i, hi⟩).2 else z.2 ⟨i, hi⟩))

def prefixPairLaw (P : Parameters) (D : ℕ) : Measure (Endpoint × Endpoint) :=
  (law P).map (fun ω => (leftEndpoint ω,
    hybridEndpoint (fun i => decide (i ∈ Finset.range D)) ω))

def prefixPairsLaw (P : Parameters) (D : ℕ) : Measure (PrefixPairs D) :=
  Measure.pi (fun i => OneCoordinateCoupling.pairLaw
    (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i))

def leftTailLaw (P : Parameters) (D : ℕ) : Measure (TailValues D) :=
  Measure.infinitePi (fun i : TailIndex D =>
    (coordinateLaw P i).map (fun z => z.2.1))

def baseTailLaw (D : ℕ) : Measure (TailValues D) :=
  Measure.infinitePi (fun _ => OneCoordinateCoupling.baseLaw)

def prefixReferenceLaw (D : ℕ) : Measure (PrefixPairs D) :=
  ∑ pattern : PrefixIndex D → Bool, Measure.pi (fun i =>
    if pattern i then OneCoordinateCoupling.triangleLaw
    else CouplingMixture.diagonal OneCoordinateCoupling.baseLaw)

def prefixReferencePairLaw (D : ℕ) : Measure (Endpoint × Endpoint) :=
  ((prefixReferenceLaw D).prod (baseTailLaw D)).map (assemblePrefixPair D)

end Invariant233.OrderedProductCoupling

end

end OAI
