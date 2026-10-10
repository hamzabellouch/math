import OAI.Geometry.SurfaceImmersion.Atlas.MetricGoodPhaseData
import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseC2Stability
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPhaseStability
import OAI.Geometry.Immersion.ClosedSurface.AtlasPartition

namespace OAI

/-! One C2 neighborhood preserves all fixed metric-adapted phase
geometry, independently of every smoothing and correction order. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry WeightedEstimates
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma compact_read_phase_C2_stability {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (i : A.centers)
    (K : TopologicalSpace.Compacts SmallModes.Base) (φ : SmallModes.Base → ℝ)
    (hφ : ContDiff ℝ ∞ φ)
    (hImm : ∀ x ∈ (K : Set SmallModes.Base),
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ x ∈ (K : Set SmallModes.Base),
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) (phaseDerivative φ x)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      ∀ b : ℝ, 0 ≤ b → b < ρ → A.WeightedBound 1 2 b (G-F) →
      ∀ x ∈ (K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i G) x) ∧
        Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x) (phaseDerivative φ x) := by
  obtain ⟨r,hr,hnear⟩ := compact_good_phase_C2_stability
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)) hφ K hImm hgood
  obtain ⟨D,hD,hd⟩ := A.vectorPlaneRead_bound (V := Space) i 2
  let L := ‖spaceCoordinates.toContinuousLinearMap‖*D
  have hL : 0 ≤ L := mul_nonneg (norm_nonneg _) hD
  have hLp : 0 < 1+L := by linarith
  refine ⟨r/(1+L),div_pos hr hLp,?_⟩
  intro G hG b hb hbr hclose
  have hread := hd (G-F) 1 b zero_lt_one le_rfl hb (hG.sub hF) hclose
  have hlocal := hread.linear uniqueDiffOn_univ zero_le_one
    (A.vectorPlaneRead_smooth i (hG.sub hF)).contDiffOn spaceCoordinates.toContinuousLinearMap
  change WeightedEstimates.WeightedBound univ 1 2 _
    (spaceCoordinates ∘ A.vectorPlaneRead i (G-F)) at hlocal
  have he : spaceCoordinates ∘ A.vectorPlaneRead i (G-F) =
      (spaceCoordinates ∘ A.vectorPlaneRead i G) - (spaceCoordinates ∘ A.vectorPlaneRead i F) := by
    rw [A.vectorPlaneRead_sub]
    funext x
    exact map_sub spaceCoordinates _ _
  rw [he] at hlocal
  have hsize : L*b < r := by
    have hh := (lt_div_iff₀ hLp).mp hbr
    nlinarith
  exact hnear (spaceCoordinates ∘ A.vectorPlaneRead i G)
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)) (L*b)
    (mul_nonneg hL hb) hsize (by simpa only [L,mul_assoc] using hlocal)

end SmoothingAtlas

private lemma phaseDerivative_linear (ξ x : SmallModes.Base) :
    phaseDerivative (phaseLinear ξ) x = ξ := by
  unfold phaseDerivative
  rw [(phaseLinear ξ).hasFDerivAt.fderiv]
  ext <;> simp [phaseLinear_apply,dx,dy]

namespace MetricGoodPhaseData

theorem uniform_C2_geometry {g : SmoothMetric M} {F : M → Space}
    (d : MetricGoodPhaseData g F) (hF : ContMDiff planeModel spaceModel ∞ F) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      ∀ b : ℝ, 0 ≤ b → b < ρ → d.A.WeightedBound 1 2 b (G-F) →
      (∀ i x, x ∈ (modeSupport (d.A.chartWeightCompact i) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ d.A.vectorPlaneRead i G) x)) ∧
      (∀ i j x, x ∈ (modeSupport (d.A.chartWeightCompact i) : Set SmallModes.Base) →
        Good (realSecondTensor (spaceCoordinates ∘ d.A.vectorPlaneRead i G) x) ((d.Q i).ξ j)) ∧
      (∀ k l x, x ∈ (modeSupport
        (d.A.quadraticOverlapCompact (fun a : d.A.centers × Fin 3 => tsupport (d.A.weight a.1))
          (fun a => isClosed_tsupport (d.A.weight a.1)) k l) : Set SmallModes.Base) →
        Good (realSecondTensor (spaceCoordinates ∘ d.A.vectorPlaneRead k G) x)
          (phaseDerivative (coordinatePhase (d.A.globalQuadraticPhase
            (d.A.linearAtlasPhase d.Q d.w) k l)) x)) := by
  classical
  have hpure (a : d.A.centers × Fin 3) := d.A.compact_read_phase_C2_stability hF a.1
    (modeSupport (d.A.chartWeightCompact a.1)) (phaseLinear ((d.Q a.1).ξ a.2))
    (phaseLinear ((d.Q a.1).ξ a.2)).contDiff (d.immersion a.1)
    (fun x hx => by simpa only [phaseDerivative_linear] using d.pure_good a.1 a.2 x hx)
  choose rp hrp hp using hpure
  let J := d.A.centers × QuadraticLabel (d.A.centers × Fin 3)
  have hquad (a : J) := d.A.compact_read_phase_C2_stability hF a.1
    (modeSupport (d.A.quadraticOverlapCompact
      (fun b : d.A.centers × Fin 3 => tsupport (d.A.weight b.1))
      (fun b => isClosed_tsupport (d.A.weight b.1)) a.1 a.2))
    (coordinatePhase (d.A.globalQuadraticPhase (d.A.linearAtlasPhase d.Q d.w) a.1 a.2))
    ((d.A.globalQuadraticPhase_smooth (d.A.linearAtlasPhase d.Q d.w)
      (d.A.linearAtlasPhase_smooth d.Q d.w) a.1 a.2).comp planeCoordinateIsometry.symm.contDiff)
    (fun x hx => d.immersion a.1 x (Set.image_mono (d.A.quadraticOverlapCompact_subset
      (fun b : d.A.centers × Fin 3 => tsupport (d.A.weight b.1))
      (fun b => isClosed_tsupport (d.A.weight b.1)) a.1 a.2) hx))
    (d.quadratic_good a.1 a.2)
  choose rq hrq hq using hquad
  obtain ⟨ρp,hρp,_,hρps⟩ := finite_positive_threshold rp hrp
  obtain ⟨ρq,hρq,_,hρqs⟩ := finite_positive_threshold rq hrq
  refine ⟨min ρp ρq,lt_min hρp hρq,?_⟩
  intro G hG b hb hbr hclose
  have hbp (a : d.A.centers × Fin 3) : b < rp a :=
    (hbr.trans_le (min_le_left _ _)).trans_le (hρps a)
  have hbq (a : J) : b < rq a :=
    (hbr.trans_le (min_le_right _ _)).trans_le (hρqs a)
  refine ⟨?_,?_,?_⟩
  · intro i x hx
    exact (hp (i,0) G hG b hb (hbp (i,0)) hclose x hx).1
  · intro i j x hx
    have hh := (hp (i,j) G hG b hb (hbp (i,j)) hclose x hx).2
    simpa only [phaseDerivative_linear] using hh
  · intro i l x hx
    exact (hq (i,l) G hG b hb (hbq (i,l)) hclose x hx).2

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
