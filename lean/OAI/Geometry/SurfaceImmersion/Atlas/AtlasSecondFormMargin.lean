import OAI.Geometry.SurfaceImmersion.Geometry.UniformSecondFormMargin
import OAI.Geometry.SurfaceImmersion.Atlas.UniformMetricPhaseGeometry

namespace OAI

/-! A single positive second-form margin for all fixed atlas supports and
all sufficiently C2-close maps. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry WeightedEstimates JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma compact_read_secondForm_C2_margin {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (i : A.centers)
    (K : TopologicalSpace.Compacts SmallModes.Base)
    (hI : ∀ x ∈ (K : Set SmallModes.Base),
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hB : ∀ x ∈ (K : Set SmallModes.Base),
      realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x ≠ 0) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ, 0 ≤ b → b < ρ →
      A.WeightedBound 1 2 b (G-F) → ∀ x ∈ (K : Set SmallModes.Base),
      c < ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ := by
  obtain ⟨r,c,hr,hc,hmargin⟩ := compact_secondForm_C2_margin
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)) K.isCompact hI hB
  obtain ⟨D,hD,hd⟩ := A.vectorPlaneRead_bound (V := Space) i 2
  let L := ‖spaceCoordinates.toContinuousLinearMap‖*D
  have hL : 0 ≤ L := mul_nonneg (norm_nonneg _) hD
  have hLp : 0 < 1+L := by linarith
  refine ⟨r/(1+L),c,div_pos hr hLp,hc,?_⟩
  intro G hG b hb hbr hclose x hx
  have hread := hd (G-F) 1 b zero_lt_one le_rfl hb (hG.sub hF) hclose
  have hlocal := hread.linear uniqueDiffOn_univ zero_le_one
    (A.vectorPlaneRead_smooth i (hG.sub hF)).contDiffOn spaceCoordinates.toContinuousLinearMap
  change WeightedEstimates.WeightedBound univ 1 2 _
    (spaceCoordinates ∘ A.vectorPlaneRead i (G-F)) at hlocal
  have he : spaceCoordinates ∘ A.vectorPlaneRead i (G-F) =
      (spaceCoordinates ∘ A.vectorPlaneRead i G)-(spaceCoordinates ∘ A.vectorPlaneRead i F) := by
    rw [A.vectorPlaneRead_sub]
    funext y
    exact map_sub spaceCoordinates _ _
  rw [he] at hlocal
  have hsize : L*b < r := by
    have hh := (lt_div_iff₀ hLp).mp hbr
    nlinarith
  exact (hmargin (spaceCoordinates ∘ A.vectorPlaneRead i G)
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)) (L*b)
    (mul_nonneg hL hb) hsize (by simpa only [L,mul_assoc] using hlocal) x hx).2

end SmoothingAtlas
namespace MetricGoodPhaseData

theorem uniform_secondForm_C2_margin {g : SmoothMetric M} {F : M → Space}
    (data : MetricGoodPhaseData g F) (hF : ContMDiff planeModel spaceModel ∞ F) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ, 0 ≤ b → b < ρ →
      data.A.WeightedBound 1 2 b (G-F) → ∀ i x,
      x ∈ (modeSupport (data.A.chartWeightCompact i) : Set SmallModes.Base) →
      c < ‖realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead i G) x‖ := by
  have hlocal (i : data.A.centers) := data.A.compact_read_secondForm_C2_margin hF i
    (modeSupport (data.A.chartWeightCompact i)) (data.immersion i) (fun x hx => by
      intro hz
      have hh := (data.pure_good i 0 x hx).2
      simp only [hz,secondQuadratic,Pi.zero_apply,smul_zero,add_zero,ne_eq,not_true_eq_false] at hh)
  choose ρ c hρ hc hmargin using hlocal
  obtain ⟨ρ₀,hρ₀,_,hρall⟩ := finite_positive_threshold ρ hρ
  obtain ⟨c₀,hc₀,_,hcall⟩ := finite_positive_threshold c hc
  refine ⟨ρ₀,c₀,hρ₀,hc₀,?_⟩
  intro G hG b hb hbρ hclose i x hx
  exact (hcall i).trans_lt (hmargin i G hG b hb (hbρ.trans_le (hρall i)) hclose x hx)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
