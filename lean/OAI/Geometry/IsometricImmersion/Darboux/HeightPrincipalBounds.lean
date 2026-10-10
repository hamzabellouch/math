import OAI.Geometry.IsometricImmersion.Flows.HeightFlowUniformBounds
import OAI.Geometry.IsometricImmersion.Energy.WeightPrimitiveParameter

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow

theorem gaussianCurvature_coordinate_bound_one_closed
    {g : MetricField} {U : Set Coord} {G d : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|) :
    CoordinateBound (gaussianCurvature g) modelSquare 1 (curvatureFirstBound G d) := by
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun i j => (hg.1 i j).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  apply CoordinateBound.of_modelSquare_interior (gaussianCurvature_contDiffOn hg hU) hU hSU
  exact gaussianCurvature_coordinate_bound_one hgI isOpen_interior hG hd
    (fun i j => (hgB i j).restrict_domain interior_subset) (fun p hp => hdet p (interior_subset hp))

end SmoothLocal.Geometry

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def heightAJetBound (G Z d c : ℝ) : ℝ :=
  2 * heightG1JetBound G Z d c *
    (curvatureFirstBound G d * (1 + flowCoordinateBound (heightQuotientJetBound G Z d c)))

theorem heightG1JetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightG1JetBound G Z d c := by
  have hQ := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hQ
  have hDG := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  dsimp [heightG1JetBound]; positivity

theorem heightAJetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightAJetBound G Z d c := by
  have hG1 := heightG1JetBound_nonneg hG hZ hd hc
  have hQ := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hQ
  have hK := curvatureFirstBound_nonneg hG hd
  dsimp [heightAJetBound]; positivity

theorem heightBJetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (ell : ℕ) :
    0 ≤ heightBJetBound G Z d c ell := by
  have hQ := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hQ
  have hP := heightPFirstBound_nonneg hG hZ hd hc
  dsimp [heightBJetBound]; positivity

theorem heightRemainderBound_nonneg {G Z d c e0 : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0) (ell : ℕ) :
    0 ≤ heightRemainderBound G Z d c e0 ell := by
  have hQ := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hQ
  have hDE := heightDriftErrorBound_nonneg hG hZ hd hc
  have hDG := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hH := hessianJetBound_nonneg hG hZ hd
  dsimp [heightRemainderBound]; positivity

theorem capFlowHeight_partial_bound_of_rho
    {q : Coord → ℝ} {Y : ℝ → ℝ → ℝ} {M : ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (hM : 0 ≤ M) (hrho : ∀ p ∈ capChartDomain, 1 / Real.exp (2 * M) ≤ capChartRho Y p)
    {p : Coord} (hp : p ∈ capChartDomain) (i : Fin 2) :
    |coordPartial i (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
  fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one]
  · rw [capFlowHeight_partial_time hY hode hp, abs_neg]
    exact (hsmall _ (hmapS hp)).trans ((by norm_num : (1 : ℝ) / 100 ≤ 1).trans
      (flowCoordinateBound_dominates hM).2.1)
  · have hpos := capFlowHeight_partial_initial_pos hY hvar hp
    rw [abs_of_pos hpos]
    have hl : 1 / Real.exp (2 * M) ≤ 1 / coordPartial 1 (capFlowHeight Y) p := hrho p hp
    have hupper : coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2 * M) := by
      simpa only [one_mul] using (div_le_div_iff₀ (Real.exp_pos _) hpos).mp hl
    exact hupper.trans (flowCoordinateBound_dominates hM).2.2.1

theorem capPullback_bound_one_from_partials
    {u : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {A F : ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hA : 0 ≤ A) (hF : 0 ≤ F) (huB : CoordinateBound u modelSquare 1 A)
    (hFB : ∀ i : Fin 2, ∀ p ∈ capChartDomain, |coordPartial i (capFlowHeight Y) p| ≤ F) :
    CoordinateBound (capPullback Y u) capChartDomain 1 (A * (1 + F)) := by
  intro ds hds p hp
  cases ds with
  | nil => exact (huB [] (by norm_num) _ (hmapS hp)).trans (by nlinarith [mul_nonneg hA hF])
  | cons i ds =>
    cases ds with
    | nil =>
      change |coordPartial i (capPullback Y u) p| ≤ A * (1 + F)
      rw [capPullback_partial hY hp ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp)) i]
      have hdu (j : Fin 2) : |coordPartial j u (capChart Y p)| ≤ A := huB [j] (by norm_num) _ (hmapS hp)
      have h0 : |if i = 0 then coordPartial 0 u (capChart Y p) else 0| ≤ A := by
        split_ifs
        · exact hdu 0
        · simpa only [abs_zero] using hA
      have h1 : |coordPartial 1 u (capChart Y p) * coordPartial i (capFlowHeight Y) p| ≤ A * F := by
        rw [abs_mul]
        exact mul_le_mul (hdu 1) (hFB i p hp) (abs_nonneg _) hA
      exact ((abs_add_le _ _).trans (add_le_add h0 h1)).trans (le_of_eq (by ring))
    | cons j ds => simp only [List.length_cons] at hds; omega

theorem heightChartA_bound_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)
    (hrho : ∀ p ∈ capChartDomain,
      1 / Real.exp (2 * heightQuotientJetBound G Z d c) ≤ capChartRho Y p)
    (hG1s : ContDiffOn ℝ ∞ (heightChartG1 g z Y) capChartDomain)
    (hG1B : CoordinateBound (heightChartG1 g z Y) capChartDomain 1 (heightG1JetBound G Z d c)) :
    CoordinateBound (heightChartA g z Y) capChartDomain 1 (heightAJetBound G Z d c) := by
  have hM := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hM
  have hK := curvatureFirstBound_nonneg hG hd
  have hG1 := heightG1JetBound_nonneg hG hZ hd hc
  have hmapU : MapsTo (capChart Y) capChartDomain U := fun p hp => hSU (hmapS hp)
  have hKs := gaussianCurvature_contDiffOn hg hU
  have hKB := capPullback_bound_one_from_partials hY hKs hU hmapU hmapS hK hF
    (gaussianCurvature_coordinate_bound_one_closed hg hU hSU hG hd hgB hdet)
    (fun i p hp => capFlowHeight_partial_bound_of_rho hY hvar hode hmapS hsmall hM hrho hp i)
  have hb := CoordinateBound.mul_through_one hG1s (capPullback_contDiffOn hY hKs hmapU)
    capChartDomain_isOpen hG1 (mul_nonneg hK (by positivity)) hG1B hKB
  exact CoordinateBound.congr_on capChartDomain_isOpen hb (fun p _ => heightChartA_eq g z Y p)

theorem heightChartB_primitive_bounds
    {g : MetricField} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ} {MB : ℝ} (ell : ℕ)
    (hB : ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain)
    (hBB : CoordinateBound (heightChartB g z Y ell) capChartDomain 1 MB)
    {p : Coord} (hp : p ∈ capChartDomain) :
    |coordinatePrimitive (heightChartB g z Y ell) p| ≤ 2 * MB ∧
    |coordPartial 1 (coordinatePrimitive (heightChartB g z Y ell)) p| ≤ 2 * MB := by
  exact ⟨coordinatePrimitive_abs_bound hB.continuousOn (by norm_num : (0 : ℝ) < 2) hp
      (fun q hq => hBB [] (by norm_num) q hq),
    coordinatePrimitive_partial_s_bound hB (by norm_num : (0 : ℝ) < 2) hp
      (fun q hq => hBB [1] (by norm_num) q hq)⟩

end SmoothLocal.Flow

end

end OAI
