import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternOrbitLaw

namespace OAI

/-! The empty spin space has constant zero pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma conditionalFieldOrbitLaw_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : Ω → FieldSpectralData 0)
    (H : Measure (Orthogonal 0)) [IsProbabilityMeasure H] :
    ConditionalFieldOrbitLaw P d (fun _ => 0) H := by
  let d0 : FieldSpectralData 0 := (fun _ => 0,fun _ => 0)
  have hd (ω : Ω) : d ω=d0 := Subsingleton.elim _ _
  have hp (z : FieldSpectralData 0 × Orthogonal 0) : dataPhysicalPressure z.1 z.2=0 := by
    simp [dataPhysicalPressure,rotatedPressure]
  unfold ConditionalFieldOrbitLaw
  rw [show d=(fun _ => d0) from funext hd]
  simp only [hp]
  simp only [Measure.map_const,measure_univ,one_smul,Measure.dirac_prod]
  rw [Measure.map_map (measurable_fst.prodMk measurable_const) measurable_prodMk_left]
  simp [Function.comp_def,Measure.map_const]

lemma gaussianPattern_conditionalOrbit_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : ℕ}
    (Z : Ω → EuclideanSpace ℝ (Fin 0 × Fin m)) (c : ℝ)
    (H : Measure (Orthogonal 0)) [IsProbabilityMeasure H] :
    ConditionalFieldOrbitLaw P
      (fun ω => (fun i => c*gaussianPatternEigenvalues (Z ω) i,fun _ => 0))
      (fun ω => gaussianPatternPressure c (Z ω)) H := by
  have hY : (fun ω => gaussianPatternPressure c (Z ω))=(fun _ : Ω => 0) := by
    funext ω
    simp [gaussianPatternPressure]
  rw [hY]
  exact conditionalFieldOrbitLaw_zero P _ H

lemma gaussianPattern_conditionalOrbit_all {Ω : Type*} [MeasurableSpace Ω]
    {N m : ℕ} (c : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → EuclideanSpace ℝ (Fin N × Fin m)) (hZ : Measurable Z)
    (hlaw : HasLaw Z (stdGaussian _) P)
    (heig : Measurable (gaussianPatternEigenvalues (N := N) (m := m)))
    (H : Measure (Orthogonal N)) [IsProbabilityMeasure H] [H.IsMulRightInvariant] :
    ConditionalFieldOrbitLaw P
      (fun ω => ((fun i => c*gaussianPatternEigenvalues (Z ω) i),fun _ => 0))
      (fun ω => gaussianPatternPressure c (Z ω)) H := by
  cases N with
  | zero => exact gaussianPattern_conditionalOrbit_zero P Z c H
  | succ n => exact gaussianPattern_conditionalOrbit_hasLaw (Nat.succ_pos n) c P Z hZ hlaw heig H

end InvariantIsing

end

end OAI
