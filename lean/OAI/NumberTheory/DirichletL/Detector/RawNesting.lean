import OAI.NumberTheory.DirichletL.Detector.RawIndexGrouping

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance : MeasurableSpace O := ⊤
local instance : MeasurableSingletonClass O := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (Ideal O) := ⊤
local instance : MeasurableSingletonClass (Ideal O) := ⟨fun _=>trivial⟩

local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩

abbrev PhysicalNestedSpace (S : Finset (Ideal O)) := SourceOuter S×(ℝ×(ℝ×(CompletedPair×(ℝ×NonzeroFrequency))))

def physicalRawNesting (S : Finset (Ideal O)) : SourceRawIndex S×HeightSpace ≃ᵐ PhysicalNestedSpace S :=
  ((sourceRawGroupingMeasurable S).prodCongr (MeasurableEquiv.refl HeightSpace)).trans physicalNestingEquiv

lemma physicalRawNesting_preserving (S : Finset (Ideal O)) :
    MeasurePreserving (physicalRawNesting S)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)
      ((Measure.count:Measure (SourceOuter S)).prod (volume.prod (volume.prod
        ((Measure.count:Measure CompletedPair).prod (volume.prod (Measure.count:Measure NonzeroFrequency)))))) := by
  exact (physicalNesting_preserving Measure.count Measure.count Measure.count volume volume volume).comp
    ((sourceRawGrouping_preserving S).prod (MeasurePreserving.id heightMeasure))

def originalNestedOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (p : PhysicalNestedSpace S) : ℂ :=
  originalRawOnLines η S hS D W0 W1 X Y Z
    ⟨(p.2.2.2.2.2,(p.2.2.2.1,p.1.val)),p.1.property⟩ ((p.2.2.1,p.2.2.2.2.1),p.2.1)

theorem originalRaw_integral_eq_nesting (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure))=
    ∑'K : SourceOuter S,∫w : ℝ,∫t : ℝ,∑'IJ : CompletedPair,∫z : ℝ,∑'H : NonzeroFrequency,
      originalNestedOnLines η S hS D W0 W1 X Y Z (K,(w,(t,(IJ,(z,H))))) := by
  have hi := originalRaw_counting_product_integrable η S hS hpS hbad D W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hp := physicalRawNesting_preserving S
  have hj := (hp.symm (physicalRawNesting S)).integrable_comp_of_integrable hi
  have he := hp.integral_comp' (originalNestedOnLines η S hS D W0 W1 X Y Z)
  have he' : (∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure))=
      ∫p : PhysicalNestedSpace S,originalNestedOnLines η S hS D W0 W1 X Y Z p
        ∂((Measure.count:Measure (SourceOuter S)).prod (volume.prod (volume.prod
          ((Measure.count:Measure CompletedPair).prod (volume.prod (Measure.count:Measure NonzeroFrequency)))))) := by
    exact he
  rw [he']
  apply integral_physical_nesting
  exact hj

end SevenEighths.ProbePhysical
end

end OAI
