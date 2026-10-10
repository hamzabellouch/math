import OAI.Analysis.KadisonKastler.CountableConjugacyAssembly
import OAI.Analysis.KadisonKastler.MeasurableConjugacyAssembly
import OAI.Analysis.KadisonKastler.SpatialConjugacyTransport
import OAI.Analysis.KadisonKastler.CenterAlgebra
import OAI.Analysis.KadisonKastler.QuotientStrongTests

namespace OAI

/-! # The published common central decomposition input

Blackadar, *Operator Algebras* (Springer, 2006), III.1.6.2--4 and
III.5.1.10--14: central decomposition on separable Hilbert space,
simultaneous decomposition of norm-separable C-star subalgebras, and
reconstruction of bounded measurable fields. The common C-star algebra is
required to commute with the common center so that it is decomposable. The dimension strata are
trivialized over standard Borel spaces with finite measures.

Only this structural input is retained. In particular, the proposition
below contains no distance estimate, implementer or stability conclusion.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

universe u

structure MeasuredHilbertStratum where
  X : Type u
  [measurableX : MeasurableSpace X]
  [standardX : StandardBorelSpace X]
  K : Type u
  [normedK : NormedAddCommGroup K]
  [innerK : InnerProductSpace ℂ K]
  [completeK : CompleteSpace K]
  [separableK : SeparableSpace K]
  [measurableK : MeasurableSpace K]
  [borelK : BorelSpace K]
  μ : Measure X
  [finiteμ : IsFiniteMeasure μ]

attribute [instance] MeasuredHilbertStratum.measurableX MeasuredHilbertStratum.standardX
  MeasuredHilbertStratum.normedK MeasuredHilbertStratum.innerK MeasuredHilbertStratum.completeK
  MeasuredHilbertStratum.separableK MeasuredHilbertStratum.measurableK
  MeasuredHilbertStratum.borelK MeasuredHilbertStratum.finiteμ

abbrev MeasuredHilbertStratum.space (S : MeasuredHilbertStratum.{u}) := Lp S.K 2 S.μ

def ScalarCenter {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (M : VonNeumannAlgebra K) : Prop :=
  ∀ T ∈ M, (∀ S ∈ M, S * T = T * S) → ∃ z : ℂ, T = z • (1 : K →L[ℂ] K)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure CentralPairDecomposition (M N : VonNeumannAlgebra H)
    (A B C : StarSubalgebra ℂ (H →L[ℂ] H)) (hAC : A ≤ C) (hBC : B ≤ C) where
  stratum : ℕ → MeasuredHilbertStratum.{u}
  coordinates : H ≃ₗᵢ[ℂ] lp (fun n => (stratum n).space) 2
  leftBlock : ∀ n, VonNeumannAlgebra (stratum n).space
  rightBlock : ∀ n, VonNeumannAlgebra (stratum n).space
  leftBlocks : BlockAlgebraDecomposition leftBlock (spatialTransportAlgebra coordinates M)
  rightBlocks : BlockAlgebraDecomposition rightBlock (spatialTransportAlgebra coordinates N)
  representation : ∀ n, (stratum n).X → C →⋆ₐ[ℂ] ((stratum n).K →L[ℂ] (stratum n).K)
  representation_measurable : ∀ n (c : C) (ξ : (stratum n).K),
    Measurable (fun x => representation n x c ξ)
  leftFields : ∀ n, OperatorFieldDecomposition (stratum n).μ
    (fun x => generatedVonNeumannAlgebra
      ((representation n x).comp (StarSubalgebra.inclusion hAC)).range) (leftBlock n)
  rightFields : ∀ n, OperatorFieldDecomposition (stratum n).μ
    (fun x => generatedVonNeumannAlgebra
      ((representation n x).comp (StarSubalgebra.inclusion hBC)).range) (rightBlock n)
  factors : ∀ n, ∀ᵐ x ∂(stratum n).μ,
    ScalarCenter (generatedVonNeumannAlgebra
      ((representation n x).comp (StarSubalgebra.inclusion hAC)).range) ∧
    ScalarCenter (generatedVonNeumannAlgebra
      ((representation n x).comp (StarSubalgebra.inclusion hBC)).range)

/-- The central case of the cited decomposition and reconstruction results,
for one pair and one chosen norm-separable common C-star algebra. -/
def PublishedCentralPairDecomposition : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SeparableSpace H], ∀ (M N : VonNeumannAlgebra H), concreteCenter M = concreteCenter N →
    ∀ (A B C : StarSubalgebra ℂ (H →L[ℂ] H)),
      IsClosed (A : Set (H →L[ℂ] H)) → IsClosed (B : Set (H →L[ℂ] H)) →
      IsClosed (C : Set (H →L[ℂ] H)) →
      IsSeparable (A : Set (H →L[ℂ] H)) → IsSeparable (B : Set (H →L[ℂ] H)) →
      IsSeparable (C : Set (H →L[ℂ] H)) →
      generatedVonNeumannAlgebra A = M → generatedVonNeumannAlgebra B = N →
      ∀ (hAC : A ≤ C) (hBC : B ≤ C),
      C ≤ (concreteCenter M).commutant.toStarSubalgebra →
      Nonempty (CentralPairDecomposition M N A B C hAC hBC)

end

end KadisonKastler

end OAI
