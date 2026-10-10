import OAI.NumberTheory.DirichletL.Detector.MixedFubini

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

abbrev SourceOuter (S : Finset (Ideal O)) := {K : Ideal O // Supported K ∧ ∀P∈S,¬P∣K}
abbrev CompletedPair := Ideal O×Ideal O

def sourceRawGrouping (S : Finset (Ideal O)) :
    SourceRawIndex S ≃ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toFun i := (⟨i.val.2.2,i.property⟩,(i.val.2.1,i.val.1))
  invFun i := ⟨(i.2.2,(i.2.1,i.1.val)),i.1.property⟩
  left_inv _i := rfl
  right_inv _i := rfl

def sourceRawGroupingMeasurable (S : Finset (Ideal O))
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    SourceRawIndex S ≃ᵐ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toEquiv := sourceRawGrouping S
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

lemma sourceRawGrouping_preserving (S : Finset (Ideal O))
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    MeasurePreserving (sourceRawGroupingMeasurable S) Measure.count
      ((Measure.count:Measure (SourceOuter S)).prod
        ((Measure.count:Measure CompletedPair).prod (Measure.count:Measure NonzeroFrequency))) := by
  rw [count_product,count_product]
  exact count_equiv_preserving _

end SevenEighths.ProbePhysical
end

end OAI
