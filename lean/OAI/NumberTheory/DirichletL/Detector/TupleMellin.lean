import OAI.NumberTheory.DirichletL.Detector.TupleScaling
import OAI.NumberTheory.DirichletL.Detector.SourceIntegrable

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def tupleSourceSeries {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (x w z : ℂ) : ℂ :=
  ∑J∈(Finset.univ:Finset (Fin K)).powerset,
    (-1:ℂ)^J.card*(elementNorm (∏i∈J,p i):ℂ)^(z-w-1)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
      (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(x+z-1)*
      sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z

def tupleSourceTripleIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→O) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    tupleSourceSeries η S C p ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

theorem compensatedTuple_eq_source_triple {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (p : Fin K→O) (hp : ∀i,p i≠0)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      tupleSourceTripleIntegral η S (calibrationForSet S hS) W0 W1 p X Y Z := by
  let A : Finset (Fin K)→ℂ := fun J=>(-1:ℂ)^J.card*
    ((elementNorm (∏i∈J,p i)^(-(3/2:ℝ)):ℝ):ℂ)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))
  let F : Finset (Fin K)→HeightSpace→ℂ := fun J t=>
    sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
      (Z*elementNorm (∏i∈Finset.univ\J,p i))
      ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    sourceRowSeries η S (calibrationForSet S hS) (Ideal.span {∏i∈Finset.univ\J,p i})
      ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
  have hF (J : Finset (Fin K)) : Integrable (F J) heightMeasure :=
    sourceRows_initial_integrable η S hS hpS hbad _ W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
      (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J)))
  have hpoint (J : Finset (Fin K)) (t : HeightSpace) :
      A J*F J t=sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
        ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
      ((-1:ℂ)^J.card*(elementNorm (∏i∈J,p i):ℂ)^(((2:ℂ)+t.1.2*Complex.I)-((3:ℂ)+t.2*Complex.I)-1)*
        star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
        (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(((3:ℂ)+t.1.1*Complex.I)+((2:ℂ)+t.1.2*Complex.I)-1)*
        sourceRowSeries η S (calibrationForSet S hS) (Ideal.span {∏i∈Finset.univ\J,p i})
          ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)) := by
    have he := sourceMellinWeight_subset W0 W1 X Y Z (elementNorm (∏i∈J,p i))
      (elementNorm (∏i∈Finset.univ\J,p i)) hX hY hZ (tuple_norm_pos p hp J)
      (tuple_norm_pos p hp (Finset.univ\J))
      (star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i)))
      ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    dsimp only [A,F]
    linear_combination (-1:ℂ)^J.card * he *
      sourceRowSeries η S (calibrationForSet S hS) (Ideal.span {∏i∈Finset.univ\J,p i})
        ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
  have hleft : compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ∑J∈(Finset.univ:Finset (Fin K)).powerset,∫t,A J*F J t ∂heightMeasure := by
    unfold compensatedTuple ProbeCompensation.tupleOperation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only
    rw [markedPhysicalProbe_eq_source_triple η S hS hpS hbad hSne _ W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
      (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J)))]
    rw [integral_const_mul]
    change A J*(((1/(2*Real.pi):ℝ):ℂ)^3*∫t,F J t ∂heightMeasure)=_
    ring
  rw [hleft,←integral_finsetSum _ (fun J _=>(hF J).const_mul (A J))]
  unfold tupleSourceTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  unfold tupleSourceSeries
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun J _=>hpoint J t)

end SevenEighths.ProbePhysical
end

end OAI
