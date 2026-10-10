import OAI.NumberTheory.DirichletL.Detector.RawNesting
import OAI.NumberTheory.DirichletL.Detector.RawNestedJoin

namespace OAI

noncomputable section
open scoped Classical
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

def rawPhysicalTotalIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)

theorem rawNestedPhysicalProbe_eq_integral (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    rawNestedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z 2 3=
      rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z := by
  unfold rawPhysicalTotalIntegral
  rw [originalRaw_integral_eq_nesting η S hS hpS hbad D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ]
  unfold rawNestedPhysicalProbe
  simp only [calibrationForSet_excluded]
  simp only [verticalIntegral,integral_const_mul,tsum_mul_left]
  unfold originalNestedOnLines originalRawOnLines
  simp only [Complex.ofReal_ofNat]
  ring_nf
  congr 1
  let e : SourceOuter S ≃ SourceOuter (calibrationForSet S hS).excluded :=
    Equiv.subtypeEquivRight (fun K=>by rw [calibrationForSet_excluded])
  rw [←e.tsum_eq]
  apply tsum_congr
  intro K
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  apply tsum_congr
  intro IJ
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  apply tsum_congr
  intro H
  congr 1 ; ring

theorem markedPhysicalProbe_eq_raw_integral (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z := by
  rw [markedPhysicalProbe_eq_nested_mellin η S hS hSne D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 2 3 hX hY hZ (by norm_num),nestedMellinPhysicalProbe_eq_raw]
  exact rawNestedPhysicalProbe_eq_integral η S hS hpS hbad D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ

end SevenEighths.ProbePhysical
end

end OAI
