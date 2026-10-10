import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternOrbit
import OAI.Probability.InvariantIsing.Pressure.PhysicalOrbitKernel

namespace OAI

/-! Haar disintegration of the actual Gaussian-pattern pressure, proved from
finite Gaussian invariance and pointwise spectral diagonalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma continuous_gaussianPatternRotation (N m : ℕ) :
    Continuous (fun p : Orthogonal N × EuclideanSpace ℝ (Fin N × Fin m) =>
      cavityColumnRotation m (matrixRotation p.1) p.2) := by
  change Continuous (fun p : Orthogonal N × EuclideanSpace ℝ (Fin N × Fin m) =>
    WithLp.toLp 2 (fun ij : Fin N × Fin m => ∑ k, (p.1 : Matrix (Fin N) (Fin N) ℝ) ij.1 k * p.2 (k,ij.2)))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ij
  apply continuous_finsetSum
  intro k _
  have hU : Continuous (fun p : Orthogonal N × EuclideanSpace ℝ (Fin N × Fin m) =>
      (p.1 : Matrix (Fin N) (Fin N) ℝ)) := continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun p : Orthogonal N × EuclideanSpace ℝ (Fin N × Fin m) =>
      (p.1 : Matrix (Fin N) (Fin N) ℝ) ij.1 k) :=
    (continuous_apply k).comp ((continuous_apply ij.1).comp hU)
  exact hu.mul ((PiLp.continuous_apply 2 _ (k,ij.2)).comp continuous_snd)

lemma gaussianPattern_orbit_kernel {N m : ℕ} (hN : 0 < N) (c : ℝ)
    (H : Measure (Orthogonal N)) [IsProbabilityMeasure H] [H.IsMulRightInvariant]
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    H.map (fun U => (((fun i => c*gaussianPatternEigenvalues z i),fun _ : Fin N => (0 : ℝ)),
      gaussianPatternPressure c (cavityColumnRotation m (matrixRotation U) z)))=
    H.map (fun U => (((fun i => c*gaussianPatternEigenvalues z i),fun _ : Fin N => (0 : ℝ)),
      dataPhysicalPressure ((fun i => c*gaussianPatternEigenvalues z i),fun _ => 0) U)) := by
  obtain ⟨V,hV⟩ := gaussianPattern_pressure_orbit c z
  exact physical_orbit_kernel hN H _ _ V hV

theorem gaussianPattern_conditionalOrbit {N m : ℕ} (hN : 0 < N) (c : ℝ)
    (heig : Measurable (gaussianPatternEigenvalues (N := N) (m := m)))
    (H : Measure (Orthogonal N)) [IsProbabilityMeasure H] [H.IsMulRightInvariant] :
    ConditionalFieldOrbitLaw (stdGaussian (EuclideanSpace ℝ (Fin N × Fin m)))
      (fun z => ((fun i => c*gaussianPatternEigenvalues z i),fun _ => 0))
      (gaussianPatternPressure c) H := by
  let d : EuclideanSpace ℝ (Fin N × Fin m) → FieldSpectralData N := fun z =>
    ((fun i => c*gaussianPatternEigenvalues z i),fun _ => 0)
  have hd : Measurable d := (measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp heig).const_mul c).prodMk measurable_const
  have hi : ∀ (U : Orthogonal N) (z : EuclideanSpace ℝ (Fin N × Fin m)),
      d (cavityColumnRotation m (matrixRotation U) z)=d z := by
    intro U z
    simp only [d,gaussianPatternEigenvalues_rotation]
  exact invariant_joint_orbit_law (stdGaussian (EuclideanSpace ℝ (Fin N × Fin m))) H
    (fun U z => cavityColumnRotation m (matrixRotation U) z)
    (continuous_gaussianPatternRotation N m).measurable
    (fun U => cavityColumnRotation_gaussian (matrixRotation U)) d
    (gaussianPatternPressure c) hd (measurable_gaussianPatternPressure N m c) hi
    dataPhysicalPressure (measurable_dataPhysicalPressure hN)
    (gaussianPattern_orbit_kernel hN c H)

theorem gaussianPattern_conditionalOrbit_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {N m : ℕ} (hN : 0 < N) (c : ℝ) (P : Measure Ω)
    (Z : Ω → EuclideanSpace ℝ (Fin N × Fin m)) (hZ : Measurable Z)
    (hlaw : HasLaw Z (stdGaussian _) P)
    (heig : Measurable (gaussianPatternEigenvalues (N := N) (m := m)))
    (H : Measure (Orthogonal N)) [IsProbabilityMeasure H] [H.IsMulRightInvariant] :
    ConditionalFieldOrbitLaw P
      (fun ω => ((fun i => c*gaussianPatternEigenvalues (Z ω) i),fun _ => 0))
      (fun ω => gaussianPatternPressure c (Z ω)) H := by
  let d := fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
    ((fun i => c*gaussianPatternEigenvalues z i),fun _ : Fin N => (0 : ℝ))
  have hd : Measurable d := (measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp heig).const_mul c).prodMk measurable_const
  have hp := measurable_gaussianPatternPressure N m c
  have hdm : P.map (fun ω => d (Z ω))=(stdGaussian _).map d := by
    change P.map (d ∘ Z)=_
    rw [← Measure.map_map hd hZ,hlaw.map_eq]
  have hym : P.map (fun ω => (d (Z ω),gaussianPatternPressure c (Z ω)))=
      (stdGaussian _).map (fun z => (d z,gaussianPatternPressure c z)) := by
    change P.map ((fun z => (d z,gaussianPatternPressure c z)) ∘ Z)=_
    rw [← Measure.map_map (hd.prodMk hp) hZ,hlaw.map_eq]
  change P.map (fun ω => (d (Z ω),gaussianPatternPressure c (Z ω)))=
    ((P.map (fun ω => d (Z ω))).prod H).map _
  rw [hym,hdm]
  exact gaussianPattern_conditionalOrbit hN c heig H

end InvariantIsing

end

end OAI
