import OAI.Geometry.SurfaceImmersion.Atlas.AnchoredAtlasPhases
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds
import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseC2Stability

namespace OAI

/-! An explicit polynomial C2 radius preserves the anchored phase family. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
lemma first_second_jet_difference_bound {F G : RField 4}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) {C : ℝ} (hC : 0 ≤ C)
    (hb : WeightedBound univ 1 2 C (F-G)) (p : Base) :
    ‖firstJetPair F p-firstJetPair G p‖ ≤ C ∧
      ‖secondJetTriple F p-secondJetTriple G p‖ ≤ C := by
  have hp := norm_realTwoJet_le (hF.sub hG) hC hb p
  change ‖realTwoJet (F-G) p‖ ≤ C at hp
  rw [realTwoJet_sub hF hG] at hp
  have hc (i : Fin 5) : ‖realTwoJet F p i-realTwoJet G p i‖ ≤ C :=
    (norm_le_pi_norm (realTwoJet F p-realTwoJet G p) i).trans hp
  constructor
  · change max ‖coordDeriv dx F p-coordDeriv dx G p‖
      ‖coordDeriv dy F p-coordDeriv dy G p‖ ≤ C
    exact max_le (hc 0) (hc 1)
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro i
    fin_cases i
    · exact hc 2
    · exact hc 3
    · exact hc 4
end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem readJetBall_radius : ∃ D : ℝ, 1 ≤ D ∧
    ∀ z : ℝ, ∀ F G : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 2 (z^4/D) (G-F) → A.ReadJetBall z F G := by
  classical
  choose E hE hread using fun i : A.centers => A.vectorPlaneRead_bound (V := Space) i 2
  let L := ‖spaceCoordinates.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  let D : ℝ := 1+∑ i : A.centers, L*E i
  have hD : 1 ≤ D := by
    have hh := Finset.sum_nonneg (s := Finset.univ) (fun i _ => mul_nonneg hL (hE i))
    change 1 ≤ 1+∑ i : A.centers, L*E i
    linarith
  have hED (i : A.centers) : L*E i ≤ D := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun i _ => mul_nonneg hL (hE i)) (Finset.mem_univ i)
    change L*E i ≤ 1+∑ i : A.centers, L*E i
    linarith
  refine ⟨D,hD,?_⟩
  intro z F G hF hG hb
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hρ : 0 ≤ z^4/D := div_nonneg (by positivity : 0 ≤ z^4) hD0.le
  refine ⟨hG,?_⟩
  intro i x _hx
  have hr := (hread i (G-F) 1 (z^4/D) zero_lt_one le_rfl hρ (hG.sub hF) hb).linear
    uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i (hG.sub hF)).contDiffOn
    spaceCoordinates.toContinuousLinearMap
  have heq : spaceCoordinates ∘ A.vectorPlaneRead i (G-F) =
      (spaceCoordinates ∘ A.vectorPlaneRead i G)-(spaceCoordinates ∘ A.vectorPlaneRead i F) := by
    funext y
    change spaceCoordinates (localize (i : M) (A.outer i) (G-F)
      (planeCoordinateIsometry.symm y)) = _
    simp only [Function.comp_apply,Pi.sub_apply,vectorPlaneRead,vectorChartRead,localize]
    by_cases hy : planeCoordinateIsometry.symm y ∈ (chart (i : M)).target
    · simp only [indicator_of_mem hy,smul_sub,map_sub]
    · simp only [indicator_of_notMem hy,map_zero,sub_self]
  change WeightedEstimates.WeightedBound univ 1 2 (L*(E i*(z^4/D)))
    (spaceCoordinates ∘ A.vectorPlaneRead i (G-F)) at hr
  rw [heq] at hr
  have hsmall : L*(E i*(z^4/D)) ≤ z^4 := by
    calc
      _ = (L*E i)*(z^4/D) := by ring
      _ ≤ D*(z^4/D) := mul_le_mul_of_nonneg_right (hED i) hρ
      _ = z^4 := by field_simp
  have hj := first_second_jet_difference_bound
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG))
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF))
    (by positivity : 0 ≤ z^4) (hr.mono_const hsmall) x
  simpa only [norm_sub_rev] using hj

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
