import OAI.Geometry.IsometricImmersion.Flows.HeightFlowBoundTools
import OAI.Geometry.IsometricImmersion.Flows.ConstructedHeightFlow

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def flowRhoJetBound (M : ℝ) : ℝ :=
  1 / Real.exp (-2 * M) + flowCoordinateBound M / (Real.exp (-2 * M))^2
def heightG1JetBound (G Z d c : ℝ) : ℝ :=
  4 * (darbouxGJetBound G Z d c * (1 + flowCoordinateBound (heightQuotientJetBound G Z d c))) *
    (flowRhoJetBound (heightQuotientJetBound G Z d c))^2
def heightBJetBound (G Z d c : ℝ) (ell : ℕ) : ℝ :=
  (heightPFirstBound G Z d c + 2 * (ell : ℝ) * heightQuotientJetBound G Z d c) *
    (1 + flowCoordinateBound (heightQuotientJetBound G Z d c))
def heightG1Lower (G Z d c e0 : ℝ) : ℝ :=
  e0 / (1 + hessianJetBound G Z d)^2 *
    (1 / Real.exp (2 * heightQuotientJetBound G Z d c))^2
def heightRemainderBound (G Z d c e0 : ℝ) (ell : ℕ) : ℝ :=
  (heightDriftErrorBound G Z d c + darbouxGJetBound G Z d c) /
      ((e0 / (1 + hessianJetBound G Z d)^2) * (1 / Real.exp (2 * heightQuotientJetBound G Z d c))) +
    (2 * (ell : ℝ) + 1) *
      (flowCoordinateBound (heightQuotientJetBound G Z d c) /
        (Real.exp (-2 * heightQuotientJetBound G Z d c))^3) /
      (1 / Real.exp (2 * heightQuotientJetBound G Z d c))^2

theorem heightG1Lower_pos {G Z d c e0 : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (he0 : 0 < e0) :
    0 < heightG1Lower G Z d c e0 := by
  have hH := hessianJetBound_nonneg hG hZ hd
  dsimp [heightG1Lower]
  positivity

theorem exists_height_flow_uniform_coefficients
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy g z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)
    (hD : ∀ p ∈ modelSquare, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    ∃ Y : ℝ → ℝ → ℝ,
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, |Y s t - s| ≤ (1 : ℝ) / 50) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) ∧
      (∀ p ∈ capChartDomain,
        0 < capChartRho Y p ∧
        1 / Real.exp (2 * heightQuotientJetBound G Z d c) ≤ capChartRho Y p ∧
        capChartRho Y p ≤ 1 / Real.exp (-2 * heightQuotientJetBound G Z d c)) ∧
      ContDiffOn ℝ ∞ (heightChartG1 g z Y) capChartDomain ∧
      CoordinateBound (heightChartG1 g z Y) capChartDomain 1 (heightG1JetBound G Z d c) ∧
      (∀ p ∈ capChartDomain, heightG1Lower G Z d c e0 ≤ heightChartG1 g z Y p) ∧
      (∀ ell : ℕ,
        ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain ∧
        CoordinateBound (heightChartB g z Y ell) capChartDomain 1 (heightBJetBound G Z d c ell) ∧
        ContDiffOn ℝ ∞ (heightChartRemainder g z Y ell) capChartDomain ∧
        ∀ p ∈ capChartDomain,
          |heightChartRemainder g z Y ell p| ≤ heightRemainderBound G Z d c e0 ell ∧
          heightChartC g z Y ell p = ((ell : ℝ) + 1) * coordPartial 1 (heightChartA g z Y) p +
            heightChartA g z Y p * heightChartRemainder g z Y ell p) := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hM
  have hH := hessianJetBound_nonneg hG hZ hd
  have hDG := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hP := heightPFirstBound_nonneg hG hZ hd hc
  have hDE := heightDriftErrorBound_nonneg hG hZ hd hc
  obtain ⟨V, hV, hSV, hVU, hVne, hqB, hEB, hGB, hPB, hΓB⟩ :=
    exists_open_low_height_coefficients hg hU hSU hz hG hZ hd hc hgB hzB hdet hyy
  have hgV : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1 i j).mono hVU, fun p hp => hg.2 p (hVU hp)⟩
  have hzV := hz.mono hVU
  have hq := hessianQuotient_contDiffOn hgV hV hzV hVne
  have hGs := darbouxG_contDiffOn hgV hV hzV hVne
  have hq1 (i : Fin 2) (p : Coord) (hp : p ∈ modelSquare) : |coordPartial i (hessianQuotient g z) p| ≤ M :=
    hqB [i] (by norm_num) p hp
  have hq2 (i j : Fin 2) (p : Coord) (hp : p ∈ modelSquare) :
      |coordPartial i (coordPartial j (hessianQuotient g z)) p| ≤ M := hqB [i, j] (by norm_num) p hp
  have hq3 (i j k : Fin 2) (p : Coord) (hp : p ∈ modelSquare) :
      |coordPartial i (coordPartial j (coordPartial k (hessianQuotient g z))) p| ≤ M :=
    hqB [i, j, k] (by norm_num) p hp
  obtain ⟨Y, hY, _, hstart, hode, _, hdisp50, hrange, _⟩ := exists_cap_flow hq hV hSV hsmall
  have hconf (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ) (ht : t ∈ Icc (-2 : ℝ) 2) :
      Y s t ∈ Icc (-3 : ℝ) 3 := abs_le.mp ((hrange s hs t ht).1.trans (by norm_num))
  have hYs := cap_flow_joint_contDiffOn hq hV hSV hY hconf hstart hode
  have hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s := fun s hs t ht =>
    cap_flow_initial_deriv_pos hq hV hSV hY hconf hstart hode hs ht
  have hdisp' (p : Coord) (hp : p ∈ capChartDomain) : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50 :=
    hdisp50 (p 1) ⟨hp.2.1.le, hp.2.2.le⟩ (p 0) ⟨hp.1.1.le, hp.1.2.le⟩
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp' p hp)
  have hmapS : MapsTo (capChart Y) capChartDomain modelSquare := fun p hp => modelOpenSquare_subset (hmapO hp)
  have hmapV : MapsTo (capChart Y) capChartDomain V := fun p hp => hSV (hmapS hp)
  have hFB := capFlowHeight_coordinate_bound hq hV hSV hY hconf hstart hode hM hsmall hq1 hq2 hq3
  have hrec (p : Coord) (hp : p ∈ capChartDomain) :=
    capReciprocal_bounds_from_q hq hV hSV hY hconf hstart hode hM hsmall hq1 hq2 hq3 hp
  have hrhoL (p : Coord) (hp : p ∈ capChartDomain) : 1 / Real.exp (2 * M) ≤ capChartRho Y p :=
    capChartRho_lower_from_q hq hV hSV hY hconf hstart hode hM (hq1 1) hp
  have hrhoJ : 0 ≤ flowRhoJetBound M := by dsimp [flowRhoJetBound]; positivity
  have hrhoB : CoordinateBound (capChartRho Y) capChartDomain 1 (flowRhoJetBound M) := by
    intro ds hds p hp
    cases ds with
    | nil =>
      exact (hrec p hp).2.1.trans (by
        dsimp [flowRhoJetBound]
        have hterm : 0 ≤ flowCoordinateBound M / (Real.exp (-2 * M))^2 := by positivity
        linarith)
    | cons i ds =>
      cases ds with
      | nil =>
        exact ((hrec p hp).2.2.1 i).trans (by
          dsimp [flowRhoJetBound]
          have hterm : 0 ≤ 1 / Real.exp (-2 * M) := by positivity
          linarith)
      | cons _ ds => simp only [List.length_cons] at hds; omega
  have hrhos := capChartRho_contDiffOn hYs hvar
  have hGrho := capPullback_bound_one hYs hGs hV hmapV hmapS hDG hF
    (hGB.mono (by norm_num) le_rfl) hFB
  have hG1B := CoordinateBound.mul_through_one (capPullback_contDiffOn hYs hGs hmapV)
    (hrhos.mul hrhos) capChartDomain_isOpen (mul_nonneg hDG (by positivity))
    (by positivity : 0 ≤ 2 * flowRhoJetBound M * flowRhoJetBound M) hGrho
    (CoordinateBound.mul_through_one hrhos hrhos capChartDomain_isOpen hrhoJ hrhoJ hrhoB hrhoB)
  have hHB := covHessian_coordinate_bound_closed_square hg hU hSU hz hG hZ hd hgB hzB hdet 1 1
  have hGfloor (p : Coord) (hp : p ∈ capChartDomain) :
      e0 / (1 + hessianJetBound G Z d)^2 ≤ darbouxG g z (capChart Y p) :=
    darbouxG_lower_of_energy_floor g z _ he0 (hEfloor _ (hmapS hp)) hH
      (hHB [] (by norm_num) _ (hmapS hp)) (hVne _ (hmapV hp))
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU, fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hD0 := fun p (hp : p ∈ modelOpenSquare) => hD p (modelOpenSquare_subset hp)
  have hE0 := fun p (hp : p ∈ modelOpenSquare) => he0.trans_le (hEfloor p (modelOpenSquare_subset hp))
  have hyy0 := fun p (hp : p ∈ modelOpenSquare) => hVne p (hSV (modelOpenSquare_subset hp))
  refine ⟨Y, capChart_contDiffOn hYs, hY, hYs, hvar, hstart, hode, hconf, hdisp50, hdisp', ?_,
    (capPullback_contDiffOn hYs hGs hmapV).mul (hrhos.pow 2), ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨(hrec p hp).1, hrhoL p hp, (le_abs_self _).trans (hrec p hp).2.1⟩
  · convert hG1B using 1 <;> first
      | (funext p; simp only [heightChartG1, pow_two])
      | (dsimp [heightG1JetBound, M]; ring)
  · intro p hp
    have hGL : 0 < e0 / (1 + hessianJetBound G Z d)^2 := by positivity
    have hGpos := hGL.trans_le (hGfloor p hp)
    have hsquare := pow_le_pow_left₀ (show 0 ≤ 1 / Real.exp (2 * M) by positivity) (hrhoL p hp) 2
    exact mul_le_mul (hGfloor p hp) hsquare (sq_nonneg _) hGpos.le
  · intro ell
    have hBB := heightOriginalB_bound_one hgV hV hSV hzV hVne (hPB 0) hqB ell
    refine ⟨heightChartB_contDiffOn hgV hV hzV hVne hYs hmapV ell, ?_,
      heightChartRemainder_contDiffOn hgO modelOpenSquare_isOpen hzO hyy0 hE0 hYs hvar hmapO ell, ?_⟩
    · exact capPullback_bound_one hYs (heightOriginalB_contDiffOn hgV hV hzV hVne ell) hV hmapV hmapS
        (by positivity : 0 ≤ heightPFirstBound G Z d c + 2 * (ell : ℝ) * M) hF hBB hFB
    · intro p hp
      refine ⟨?_, heightChartC_factor hgO modelOpenSquare_isOpen hzO hD0 hyy0 hE0 hYs hvar hmapO hp ell⟩
      exact heightChartRemainder_bound_of_low_coefficients g z Y p ell hDE hDG
        (show 0 ≤ flowCoordinateBound M / (Real.exp (-2 * M))^3 by positivity)
        (show 0 < e0 / (1 + hessianJetBound G Z d)^2 by positivity)
        (show 0 < 1 / Real.exp (2 * M) by positivity)
        (curvatureDriftError_bound_original_data hG hZ hc hgB hzB hEB hHB hΓB hyy hsmall (hmapS hp))
        (hGB [1] (by norm_num) _ (hmapS hp)) (hGfloor p hp) (hrhoL p hp) (hrec p hp).2.2.2.1

end SmoothLocal.Flow

end

end OAI
