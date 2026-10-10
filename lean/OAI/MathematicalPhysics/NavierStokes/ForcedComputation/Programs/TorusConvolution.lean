import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.CompactParameterIntegral
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorScalarTranslation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatEvolutionSmooth
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatPeriodicity

namespace OAI

/-! Spatial differentiation of the heat convolution by differentiating the data.
Translation invariance of the periodic cell removes derivatives of the kernel. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped ContDiff

def weightedShiftIntegral (k g : Plane → ℝ) (x : Plane) : ℝ :=
  ∫ y in Icc (0 : Plane) (fun _ => 1), k y * g (x+y)

private abbrev Cell := Icc (0 : Plane) (fun _ => 1)
private instance : CompactSpace Cell := isCompact_iff_compactSpace.mp isCompact_Icc
local instance : MeasureSpace Cell := Measure.Subtype.measureSpace
private instance : IsFiniteMeasure (volume : Measure Cell) := by
  constructor
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  exact (isCompact_Icc : IsCompact (Icc (0 : Plane) (fun _ => 1))).measure_lt_top

theorem weightedShiftIntegral_smooth {k g : Plane → ℝ}
    (hk : Continuous k) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (weightedShiftIntegral k g) := by
  let f : Plane × ℝ → ℝ := fun q => q.2 * g q.1
  have hf : ContDiff ℝ ∞ f := contDiff_snd.mul (hg.comp contDiff_fst)
  let b : C(Cell, Plane × ℝ) := ⟨fun y => ((y : Plane), k y),
    continuous_subtype_val.prodMk (hk.comp continuous_subtype_val)⟩
  let A : Plane →L[ℝ] C(Cell, Plane × ℝ) :=
    (ContinuousLinearMap.const ℝ Cell).comp (ContinuousLinearMap.inl ℝ Plane ℝ)
  have h := Flow.contDiff_compactIntegral (volume : Measure Cell)
    (⟨f, hf.continuous⟩ : C(Plane × ℝ, ℝ)) hf (fun x => A x+b)
    (A.contDiff.add contDiff_const)
  convert h using 1
  funext x
  rw [weightedShiftIntegral, ← integral_subtype measurableSet_Icc]
  congr 1
  funext y
  change k y * g (x+(y : Plane)) = (0+k y) * g (x+(y : Plane))
  rw [zero_add]

theorem weightedShiftIntegral_fderiv {k g : Plane → ℝ}
    (hk : Continuous k) (hg : ContDiff ℝ ∞ g) (x v : Plane) :
    fderiv ℝ (weightedShiftIntegral k g) x v =
      weightedShiftIntegral k (fun y => fderiv ℝ g y v) x := by
  let W : ℝ → Plane → ℝ := fun s y => k y * g (x+s • v+y)
  let D : ℝ → Plane → ℝ := fun s y => k y * fderiv ℝ g (x+s • v+y) v
  have hi : ContDiff ℝ ∞ (fun p : ℝ × Plane => x+p.1 • v+p.2) :=
    (contDiff_const.add (contDiff_fst.smul contDiff_const)).add contDiff_snd
  have hW : Continuous (Function.uncurry W) :=
    (hk.comp continuous_snd).mul (hg.comp hi).continuous
  have hD : Continuous (Function.uncurry D) :=
    (hk.comp continuous_snd).mul
      (((hg.fderiv_right (by simp)).comp hi).clm_apply contDiff_const).continuous
  have hd (s : ℝ) (y : Plane) : HasDerivAt (fun r => W r y) (D s y) s := by
    have h := ((hg.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
      ((((hasDerivAt_id s).smul_const v).const_add x).add_const y)).const_mul (k y)
    simpa only [W, D, Function.comp_def, id_eq, one_smul] using h
  have h₁ := scalarMass_hasDerivAt hW hD hd 0
  have hl : HasDerivAt (fun s : ℝ => x+s • v) v 0 := by
    simpa only [id_eq, one_smul] using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
  have h₂ := ((weightedShiftIntegral_smooth hk hg).differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h := h₂.unique h₁
  simpa only [scalarMass, W, D, weightedShiftIntegral, Function.comp_def,
    id_eq, zero_smul, add_zero, one_smul] using h

theorem torusHeatEvolution_eq_shift {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : PlanePeriodic g) {t : ℝ} (ht : 0 < t) (x : Plane) :
    torusHeatEvolution g t x = weightedShiftIntegral (fun y => torusHeatKernel t (-y)) g x := by
  let f : Plane → ℝ := fun y => torusHeatKernel t (x-y) * g y
  have hks : ContDiff ℝ ∞ (torusHeatKernel t) := by
    have h := torusHeatKernel_smooth_positive.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn
      (show MapsTo (fun y : Plane => (t, y)) univ (Ioi (0 : ℝ) ×ˢ univ) from
        fun _ _ => ⟨ht, mem_univ _⟩)
    simpa only [Function.comp_def, id_eq, contDiffOn_univ] using h
  have hf : ContDiff ℝ ∞ f :=
    (hks.comp (contDiff_const.sub contDiff_id)).mul hg
  have hfp : PlanePeriodic f := by
    intro y n
    dsimp [f]
    rw [hp y n]
    have he : x-(y+fun j => (n j : ℝ)) = (x-y)+fun j => ((-n j : ℤ) : ℝ) := by
      ext j
      simp only [Pi.sub_apply, Pi.add_apply, Int.cast_neg]
      ring
    rw [he, torusHeatKernel_periodic ht (x-y) (fun j => -n j)]
  have hi := CompactCenter.integral_translated hf hfp x
  rw [torusHeatEvolution, ite_eq_right (not_le.mpr ht)]
  unfold weightedShiftIntegral
  convert hi.symm using 1
  congr 1
  funext y
  dsimp [f]
  rw [show x-(y+x) = -y by abel, add_comm y x]

theorem torusHeatEvolution_spatialD {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : PlanePeriodic g) (t : ℝ) (j : Fin 2) :
    PlanarHamiltonian.spatialD j (torusHeatEvolution g t) =
      torusHeatEvolution (PlanarHamiltonian.spatialD j g) t := by
  by_cases ht : t ≤ 0
  · have he (f : Plane → ℝ) : torusHeatEvolution f t = f := by
      funext x
      simp only [torusHeatEvolution, ite_eq_left ht]
    rw [he g, he (PlanarHamiltonian.spatialD j g)]
  · have ht' : 0 < t := lt_of_not_ge ht
    have he : torusHeatEvolution g t =
        weightedShiftIntegral (fun y => torusHeatKernel t (-y)) g :=
      funext (torusHeatEvolution_eq_shift hg hp ht')
    funext x
    have hk : Continuous (fun y : Plane => torusHeatKernel t (-y)) :=
      (torusHeatKernel_continuous ht').comp continuous_neg
    rw [PlanarHamiltonian.spatialD, he, weightedShiftIntegral_fderiv hk hg]
    exact (torusHeatEvolution_eq_shift (PlanarHamiltonian.spatialD_smooth j hg)
      (spatialD_periodic hg hp j) ht' x).symm

end ForcedComputation.VelocityDetector

end

end OAI
