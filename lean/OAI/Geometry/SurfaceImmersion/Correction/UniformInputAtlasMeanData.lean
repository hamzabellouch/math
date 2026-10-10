import OAI.Geometry.SurfaceImmersion.Correction.UniformLinearChartedMeanFamily
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPhaseStability
import OAI.Geometry.Immersion.ClosedSurface.AtlasPartition

namespace OAI

/-! Fixed atlas mean profiles from the global norms of the actual input map. -/
noncomputable section
open Set Manifold TopologicalSpace
open scoped ContDiff Manifold Topology NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- The fixed local geometry determines all mean profiles and one global C2
radius before the nearby map, the scales, and the smaller trial radius. -/
theorem uniform_input_atlas_mean_data_all_profiles
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (Ω U K : A.centers → Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ i j, IsOpen (Ω i j)) (hU : ∀ i j, IsOpen (U i j))
    (hK : ∀ i j, IsCompact (K i j))
    (hUK : ∀ i j, U i j ⊆ K i j) (hKΩ : ∀ i j, K i j ⊆ Ω i j)
    (ξ : A.centers → Fin 3 → SmallModes.Base) (hξ : ∀ i j, ξ i j ≠ 0)
    (hImm : ∀ i j x, x ∈ Ω i j → Function.Injective
      (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ Ω i j →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) (ξ i j))
    (S : A.centers → Fin 3 → Compacts JetPolynomial.Base)
    (hS : ∀ i j, (modeSupport (S i j) : Set SmallModes.Base) ⊆ U i j)
    (U₀ : A.centers → Set JetPolynomial.Base) (hU₀ : ∀ i, IsOpen (U₀ i))
    (K₀ : A.centers → Compacts JetPolynomial.Base)
    (hU₀K : ∀ i, U₀ i ⊆ K₀ i) (hSU₀ : ∀ i j, (S i j : Set JetPolynomial.Base) ⊆ U₀ i)
    (φ : A.centers → Fin 3 → JetPolynomial.Base → ℝ)
    (hφ : ∀ i j, ContDiff ℝ ∞ (φ i j))
    (hphase : ∀ i j, coordinatePhase (φ i j) = phaseLinear (ξ i j))
    (ψ : ∀ i j, SupportedField (F := ℝ)
      (JetPolynomial.chartSupport (linearPhaseChart (ξ i j) (hξ i j) (U i j) (hU i j))
        (modeSupport (S i j)) (hS i j)))
    (Q : A.centers → Fin 3 → Tensor →L[ℝ] ℝ) {r ρ R : ℝ}
    (reference : A.centers → SmallModes.Base → Tensor)
    (hmargin : ∀ i j x, x ∈ U i j → ρ + ‖Q i j‖*r ≤ Q i j (reference i x) ∧
      Q i j (reference i x) ≤ R - ‖Q i j‖*r)
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (P : ℕ → ℝ), (∀ m, 0 ≤ P m) →
    ∃ p : A.centers → Fin 3 → ChartedMeanProfile emptyMetricPolynomial,
      ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G) (B : ℝ),
        0 ≤ B → B < ρ₀ → A.WeightedBound 1 2 B (G-F) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
        ∀ (τ r' : ℝ), r' ≤ r →
        ∃ d : ∀ i, ChartedMeanFamilyData emptyMetricPolynomial 0 τ s r' ρ R (reference i),
          (∀ i, (d i).Fits (p i)) ∧
          (∀ i, (d i).G = A.jetChartMap i G) ∧
          (∀ i, (d i).phase = φ i) ∧ (∀ i, (d i).support = S i) ∧
          (∀ i j, ((d i).solver j).e =
            linearPhaseChart (ξ i j) (hξ i j) (U i j) (hU i j)) ∧
          (∀ i j x, ((d i).data j).cutoff x = ψ i j x) ∧
          (∀ i j, ((d i).data j).form = fun _ => Q i j) := by
  classical
  let e := fun i j => linearPhaseChart (ξ i j) (hξ i j) (U i j) (hU i j)
  let KV : A.centers → Fin 3 → Compacts SmallModes.Base := fun i j =>
    ⟨(phaseEquiv (ξ i j) (hξ i j)) '' K i j,
      (hK i j).image (phaseEquiv (ξ i j) (hξ i j)).continuous⟩
  have htarget (i j) : (e i j).target ⊆ KV i j := image_mono (hUK i j)
  choose E hE he using fun (i : A.centers) (j : Fin 3) (m : ℕ) =>
    A.phaseChart_twoJet_bound i (linearPhaseChart_smooth (ξ i j) (hξ i j) (U i j) (hU i j)).2
      (KV i j) (e i j).open_target (htarget i j) m
  choose V hV hv using fun (i : A.centers) (m : ℕ) =>
    A.vectorPlaneRead_prefix_bounds (V := Space) i 2 m
  choose V₀ hV₀ hv₀ using fun i : A.centers => A.vectorPlaneRead_bound (V := Space) i 2
  let L : ℝ := ‖spaceCoordinates.toContinuousLinearMap‖
  choose a ha hall using fun i : A.centers => uniform_linear_charted_mean_family_all_profiles
    (A.jetChartMap_smooth i hF) (Ω i) (U i) (K i) (hΩ i) (hU i) (hK i) (hUK i) (hKΩ i)
    (ξ i) (hξ i)
    (by simpa only [A.jetChartMap_plane] using hImm i)
    (by simpa only [A.jetChartMap_plane] using hgood i)
    (S i) (hS i) (hU₀ i) (K₀ i) (hU₀K i) (hSU₀ i) (φ i) (hφ i) (hphase i)
    (ψ i) (Q i) (hmargin i)
  have hL₀ (i) : 0 ≤ L * V₀ i := mul_nonneg (norm_nonneg _) (hV₀ i)
  obtain ⟨ρ₀,hρ₀,_,hρa⟩ := finite_positive_threshold
    (fun i : A.centers => a i / (1 + L * V₀ i))
    (fun i => div_pos (ha i) (by linarith [hL₀ i]))
  refine ⟨ρ₀,hρ₀,?_⟩
  intro P hP
  let H : A.centers → Fin 3 → ℕ → ℝ := fun i j m => 1 + E i j m * P m
  let Pjet : A.centers → ℕ → ℝ := fun i m => L * V i m * P m
  have hH (i j m) : 1 ≤ H i j m :=
    le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans (hE i j m)) (hP m))
  have hPjet (i m) : 0 ≤ Pjet i m :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (hV i m)) (hP m)
  choose p _ _ _ hdata using fun i => hall i (H i) (Pjet i) (hH i) (hPjet i)
  refine ⟨p,?_⟩
  intro G hG B hB hBρ hclose s hs hs1 hp τ r' hr
  have hsmall (i) : L * V₀ i * B < a i := by
    have hh := (lt_div_iff₀ (show 0 < 1 + L * V₀ i by linarith [hL₀ i])).mp
      (hBρ.trans_le (hρa i))
    nlinarith
  have hlocalClose (i) : WeightedEstimates.WeightedBound univ 1 2 (L * V₀ i * B)
      ((A.jetChartMap i G ∘ planeCoordinateIsometry.symm) -
        (A.jetChartMap i F ∘ planeCoordinateIsometry.symm)) := by
    have hh := (hv₀ i (G-F) 1 B zero_lt_one le_rfl hB (hG.sub hF) hclose).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i (hG.sub hF)).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    simp only [ContinuousLinearEquiv.coe_coe] at hh
    change WeightedEstimates.WeightedBound univ 1 2 _
      (spaceCoordinates ∘ A.vectorPlaneRead i (G-F)) at hh
    have hsub : spaceCoordinates ∘ A.vectorPlaneRead i (G-F) =
        (spaceCoordinates ∘ A.vectorPlaneRead i G) -
          (spaceCoordinates ∘ A.vectorPlaneRead i F) := by
      rw [A.vectorPlaneRead_sub]
      funext x
      exact map_sub spaceCoordinates _ _
    rw [hsub] at hh
    simpa only [A.jetChartMap_plane,L,mul_assoc] using hh
  have hlocalJets (i j m) : WeightedEstimates.WeightedBound (e i j).target s m (H i j m)
      (realTwoJet ((A.jetChartMap i G ∘ planeCoordinateIsometry.symm) ∘ (e i j).symm)) := by
    have hh := he i j m G s (P m) hs hs1 (hP m) hG (hp m)
    apply (show WeightedEstimates.WeightedBound (e i j).target s m (E i j m * P m)
      (realTwoJet ((A.jetChartMap i G ∘ planeCoordinateIsometry.symm) ∘ (e i j).symm)) from
      by simpa only [A.jetChartMap_plane] using hh).mono_const
    exact le_add_of_nonneg_left zero_le_one
  have hprefix (i m j) (hj : j ≤ m+2) : WeightedEstimates.WeightedBound (U₀ i) 1 j
      (Pjet i m / (s : ℝ)^(j-2)) (A.jetChartMap i G) := by
    have hread := (hv i m G s (P m) hs hs1 (hP m) hG (hp m) j (by omega)).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i hG).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    have hcoordinate := weightedBound_comp_isometry planeCoordinateIsometry
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)) hread
    have heq : (spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ planeCoordinateIsometry =
        A.jetChartMap i G := by
      funext x
      have hx := congrFun (A.jetChartMap_plane i G) (planeCoordinateIsometry x)
      simpa only [Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] using hx.symm
    rw [heq] at hcoordinate
    have hjet : WeightedEstimates.WeightedBound univ 1 j
        (Pjet i m / (s : ℝ)^(j-2)) (A.jetChartMap i G) := by
      simpa only [Pjet,L,mul_div_assoc,mul_assoc] using hcoordinate
    exact hjet.restrict_open (hU₀ i)
  choose d hfit hmap hphase' hsupp he' hcut hform using fun i : A.centers =>
    hdata i (A.jetChartMap i G) (A.jetChartMap_smooth i hG) (L * V₀ i * B)
      (mul_nonneg (hL₀ i) hB) (hsmall i) (hlocalClose i) s hs hs1 (hlocalJets i)
      (hprefix i) τ r' hr
  exact ⟨d,hfit,hmap,hphase',hsupp,he',hcut,hform⟩

/-- The fixed local geometry determines all mean profiles and one global C2
radius before the nearby map, the scales, and the smaller trial radius. -/
theorem uniform_input_atlas_mean_data
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (Ω U K : A.centers → Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ i j, IsOpen (Ω i j)) (hU : ∀ i j, IsOpen (U i j))
    (hK : ∀ i j, IsCompact (K i j))
    (hUK : ∀ i j, U i j ⊆ K i j) (hKΩ : ∀ i j, K i j ⊆ Ω i j)
    (ξ : A.centers → Fin 3 → SmallModes.Base) (hξ : ∀ i j, ξ i j ≠ 0)
    (hImm : ∀ i j x, x ∈ Ω i j → Function.Injective
      (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ Ω i j →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) (ξ i j))
    (S : A.centers → Fin 3 → Compacts JetPolynomial.Base)
    (hS : ∀ i j, (modeSupport (S i j) : Set SmallModes.Base) ⊆ U i j)
    (U₀ : A.centers → Set JetPolynomial.Base) (hU₀ : ∀ i, IsOpen (U₀ i))
    (K₀ : A.centers → Compacts JetPolynomial.Base)
    (hU₀K : ∀ i, U₀ i ⊆ K₀ i) (hSU₀ : ∀ i j, (S i j : Set JetPolynomial.Base) ⊆ U₀ i)
    (φ : A.centers → Fin 3 → JetPolynomial.Base → ℝ)
    (hφ : ∀ i j, ContDiff ℝ ∞ (φ i j))
    (hphase : ∀ i j, coordinatePhase (φ i j) = phaseLinear (ξ i j))
    (ψ : ∀ i j, SupportedField (F := ℝ)
      (JetPolynomial.chartSupport (linearPhaseChart (ξ i j) (hξ i j) (U i j) (hU i j))
        (modeSupport (S i j)) (hS i j)))
    (Q : A.centers → Fin 3 → Tensor →L[ℝ] ℝ) {r ρ R : ℝ}
    (reference : A.centers → SmallModes.Base → Tensor)
    (hmargin : ∀ i j x, x ∈ U i j → ρ + ‖Q i j‖*r ≤ Q i j (reference i x) ∧
      Q i j (reference i x) ≤ R - ‖Q i j‖*r)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) :
    ∃ (ρ₀ : ℝ) (p : A.centers → Fin 3 → ChartedMeanProfile emptyMetricPolynomial),
      0 < ρ₀ ∧ ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G) (B : ℝ),
        0 ≤ B → B < ρ₀ → A.WeightedBound 1 2 B (G-F) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
        ∀ (τ r' : ℝ), r' ≤ r →
        ∃ d : ∀ i, ChartedMeanFamilyData emptyMetricPolynomial 0 τ s r' ρ R (reference i),
          (∀ i, (d i).Fits (p i)) ∧
          (∀ i, (d i).G = A.jetChartMap i G) ∧
          (∀ i, (d i).phase = φ i) ∧ (∀ i, (d i).support = S i) ∧
          (∀ i j, ((d i).solver j).e =
            linearPhaseChart (ξ i j) (hξ i j) (U i j) (hU i j)) ∧
          (∀ i j x, ((d i).data j).cutoff x = ψ i j x) ∧
          (∀ i j, ((d i).data j).form = fun _ => Q i j) := by
  obtain ⟨ρ₀,hρ₀,hall⟩ := A.uniform_input_atlas_mean_data_all_profiles F hF Ω U K hΩ hU hK
    hUK hKΩ ξ hξ hImm hgood S hS U₀ hU₀ K₀ hU₀K hSU₀ φ hφ hphase ψ Q reference hmargin
  obtain ⟨p,hdata⟩ := hall P hP
  exact ⟨ρ₀,p,hρ₀,hdata⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
