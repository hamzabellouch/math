import OAI.NumberTheory.DirichletL.Detector.CompensatedTriple

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def highRowOnLines (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (u : NonzeroFrequency) (t : HeightSpace) : ℂ :=
  star (C.residueMonoid u.val)*frequencyWeight ((ξ:ℂ)+t.1.2*Complex.I) u*
    markedIdealHighSeries S D η u.val ((σ:ℂ)+t.1.1*Complex.I)
      ((υ:ℂ)+t.2*Complex.I) ((ξ:ℂ)+t.1.2*Complex.I)

lemma highRowOnLines_eq_tsum (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (u : NonzeroFrequency) (t : HeightSpace) :
    highRowOnLines η S C D σ υ ξ u t=
      ∑'q : (Id×Id)×(Id×Id),initialHighOnLines S D η (fun H=>star (C.residueMonoid H.val))
        σ υ ξ (u,q) t := by
  unfold highRowOnLines markedIdealHighSeries initialHighOnLines fullHighCoefficient
  exact (tsum_mul_left (a:=star (C.residueMonoid u.val)*frequencyWeight ((ξ:ℂ)+t.1.2*Complex.I) u)
    (f:=fun q : (Id×Id)×(Id×Id)=>markedIdealHighSummand S D η u.val
      ((σ:ℂ)+t.1.1*Complex.I) ((υ:ℂ)+t.2*Complex.I) ((ξ:ℂ)+t.1.2*Complex.I)
      q.1.1 q.1.2 q.2.1 q.2.2)).symm

lemma initialHighMajorant_row_summable (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1/6<ξ)
    (u : NonzeroFrequency) : Summable (fun q : (Id×Id)×(Id×Id)=>initialHighMajorant σ υ ξ (u,q)) := by
  unfold initialHighMajorant
  exact (highAbsoluteMajorant_summable (σ:ℂ) (υ:ℂ) (ξ:ℂ) hσ hυ hξ).mul_left ‖frequencyWeight (ξ:ℂ) u‖

lemma highRowOnLines_continuous (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1/6<ξ) (u : NonzeroFrequency) :
    Continuous (highRowOnLines η S C D σ υ ξ u) := by
  change Continuous (fun t=>highRowOnLines η S C D σ υ ξ u t)
  simp_rw [highRowOnLines_eq_tsum]
  apply continuous_tsum _ (initialHighMajorant_row_summable σ υ ξ hσ hυ hξ u)
    (fun q t=>initialHighOnLines_norm_le S D η (fun H=>star (C.residueMonoid H.val))
      (fun H=>by simpa only [norm_star] using C.residueMonoid_norm_le_one H.val) σ υ ξ (u,q) t)
  intro q
  exact initialHighOnLines_continuous S D η _ σ υ ξ (u,q)

lemma highRowOnLines_bound (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1/6<ξ) (u : NonzeroFrequency) (t : HeightSpace) :
    ‖highRowOnLines η S C D σ υ ξ u t‖≤
      ‖frequencyWeight (ξ:ℂ) u‖*(∑'q : (Id×Id)×(Id×Id),highAbsoluteMajorant (σ:ℂ) (υ:ℂ) (ξ:ℂ) q) := by
  rw [highRowOnLines_eq_tsum]
  have hm := initialHighMajorant_row_summable σ υ ξ hσ hυ hξ u
  have hb (q : (Id×Id)×(Id×Id)) := initialHighOnLines_norm_le S D η
    (fun H=>star (C.residueMonoid H.val))
    (fun H=>by simpa only [norm_star] using C.residueMonoid_norm_le_one H.val) σ υ ξ (u,q) t
  have hs := Summable.of_nonneg_of_le (fun q=>norm_nonneg _) hb hm
  apply (norm_tsum_le_tsum_norm hs).trans
  have he := hs.tsum_le_tsum hb hm
  simpa only [initialHighMajorant,tsum_mul_left] using he

lemma highRows_counting_product_integrable {ρ : Type*} [Countable ρ]
    [MeasurableSpace ρ] [MeasurableSingletonClass ρ]
    (e : ρ→NonzeroFrequency) (he : Function.Injective e)
    (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) (hcT : Continuous T) :
    Integrable (fun p : ρ×HeightSpace=>highRowOnLines η S C D σ υ ξ (e p.1) p.2*T p.2)
      ((Measure.count:Measure ρ).prod heightMeasure) := by
  let A : ℝ := ∑'q : (Id×Id)×(Id×Id),highAbsoluteMajorant (σ:ℂ) (υ:ℂ) (ξ:ℂ) q
  have hA : 0≤A := tsum_nonneg (highAbsoluteMajorant_nonneg _ _ _)
  have hb : Integrable (fun r : ρ=>‖frequencyWeight (ξ:ℂ) (e r)‖*A) Measure.count := by
    rw [integrable_count_iff]
    simpa only [Function.comp_def,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) hA)] using
      ((frequencyWeight_summable_norm (ξ:ℂ) hξ).comp_injective he).mul_right A
  apply (hb.mul_prod hT.norm).mono'
  · apply Measurable.aestronglyMeasurable
    apply measurable_from_prod_countable_right
    intro r
    exact ((highRowOnLines_continuous η S C D σ υ ξ hσ hυ (by linarith) (e r)).mul hcT).measurable
  · apply Filter.Eventually.of_forall
    intro p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (highRowOnLines_bound η S C D σ υ ξ hσ hυ (by linarith) (e p.1) p.2) (norm_nonneg _)

end SevenEighths.ProbePhysical
end

end OAI
