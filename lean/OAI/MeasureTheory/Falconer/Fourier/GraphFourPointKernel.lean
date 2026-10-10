import OAI.MeasureTheory.Falconer.Graphs.GraphEndpointContinuity
import OAI.MeasureTheory.Falconer.Graphs.GraphGlobalPhase

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def graphFourAmplitude (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane)
    (u v : UnitCircle) : ℂ :=
  W (u,v) * (b 0 (x 0) u * conj (b 1 (x 1) u)) *
    (b 2 (x 2) v * conj (b 3 (x 3) v))

noncomputable def graphFourKernel (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane)
    (r : ℝ) (u v : UnitCircle) : ℂ :=
  (sourcePlaneWave r u (x 0-x 1) * sourcePlaneWave r v (x 2-x 3)) *
    graphFourAmplitude b W x u v

theorem graphFourKernel_continuous (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane)
    (hb : ∀ i, Continuous (b i (x i))) (hW : Continuous W) :
    Continuous (fun p : ℝ × (UnitCircle × UnitCircle) =>
      graphFourKernel b W x p.1 p.2.1 p.2.2) := by
  have hu : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hv : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => p.2.2) :=
    continuous_snd.comp continuous_snd
  exact (((sourcePlaneWave_continuous _).comp (continuous_fst.prodMk hu)).mul
    ((sourcePlaneWave_continuous _).comp (continuous_fst.prodMk hv))).mul
      (((hW.comp continuous_snd).mul
        ((hb 0 |>.comp hu).mul (Complex.continuous_conj.comp (hb 1 |>.comp hu)))).mul
        ((hb 2 |>.comp hv).mul (Complex.continuous_conj.comp (hb 3 |>.comp hv))))

theorem graphFourKernel_chart (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane)
    (hb : ∀ i, Continuous (b i (x i))) (hW : Continuous W)
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {R : ℝ} (hR : 0 < R) (axis : ℝ) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • graphFourKernel b W x r u v
      ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalAnnulus (1/4) 4 z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          (Ψ (‖η‖*Real.sqrt (1+z^2)/2) •
            graphFourKernel b W x (R*(‖η‖*Real.sqrt (1+z^2)/2))
              (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
              (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis))) :=
  sourceArcLength_pair_graph_annulus_bump (graphFourKernel_continuous b W x hb hW)
    hΨ hsupp hR axis

theorem actual_inherited_graphFourKernel_chart
    {ι : Fin 4 → Type*} (S : ∀ a, Finset (ι a)) (d : ∀ a, ι a → PolicyDescriptor)
    (k : ∀ a, ι a → ℕ) (Q : Fin 4 → DyadicSquare) (hQ : ∀ a, 0 < (Q a).side)
    (ρ : Fin 4 → Measure Plane) (m : Fin 4 → ℝ → ℝ) (N : ℕ)
    (lam sig : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane)
    (W : UnitCircle × UnitCircle → ℂ) (hW : Continuous W)
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {R : ℝ} (hR : 0 < R) (axis : ℝ) :
    let b := fun a => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (m a)
      N lam sig J i (h a)
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • graphFourKernel b W x r u v
      ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalAnnulus (1/4) 4 z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          (Ψ (‖η‖*Real.sqrt (1+z^2)/2) •
            graphFourKernel b W x (R*(‖η‖*Real.sqrt (1+z^2)/2))
              (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
              (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis))) := by
  dsimp only
  exact graphFourKernel_chart _ W x
    (fun a => inheritedCircleSymbol_continuous (S a) (d a) (k a) (Q a) (hQ a)
      (ρ a) (m a) N lam sig J i (h a) (x a)) hW hΨ hsupp hR axis

theorem graphFourKernel_phase_plus (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane)
    {η : Plane} (hη : η ∈ graphPlaneSlit) (z R : ℝ) :
    graphFourKernel b W x (R*(‖η‖*Real.sqrt (1+z^2)/2))
        (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
        (sourceUnitDirection (graphPlaneAngle η-Real.arctan z)) =
      Complex.exp (Complex.I*(R:ℂ)*
        (inner ℝ η (graphA z (x 0-x 1)+graphB z (x 2-x 3)) : ℂ)) *
        graphFourAmplitude b W x
          (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
          (sourceUnitDirection (graphPlaneAngle η-Real.arctan z)) := by
  rw [graphFourKernel, graph_global_plane_wave_phase hη]

theorem graphFourKernel_phase_minus (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (x : Fin 4 → Plane)
    {η : Plane} (hη : η ∈ graphPlaneSlit) (z R : ℝ) :
    graphFourKernel b W x (R*(‖η‖*Real.sqrt (1+z^2)/2))
        (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
        (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+Real.pi)) =
      Complex.exp (Complex.I*(R:ℂ)*
        (inner ℝ η (graphA z (x 0-x 1)-graphB z (x 2-x 3)) : ℂ)) *
        graphFourAmplitude b W x
          (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
          (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+Real.pi)) := by
  rw [graphFourKernel, graph_global_plane_wave_phase_minus hη]

end PlanarFalconer

end OAI
