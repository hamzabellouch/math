import OAI.Geometry.IsometricImmersion.Darboux.HeightPrincipalBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def heightCapCurvatureBound (G Z d c : ℝ) : ℝ :=
  curvatureFirstBound G d*(1+flowCoordinateBound (heightQuotientJetBound G Z d c))

def heightCapCValueBound (G Z d c e0 : ℝ) (ell : ℕ) : ℝ :=
  ((ell : ℝ)+1)*heightAJetBound G Z d c +
    heightAJetBound G Z d c*heightRemainderBound G Z d c e0 ell

def heightCapCoefficientBound (G Z d c e0 : ℝ) (ell : ℕ) : ℝ :=
  heightAJetBound G Z d c + 2*heightBJetBound G Z d c ell + heightCapCValueBound G Z d c e0 ell

theorem heightCapCurvatureBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightCapCurvatureBound G Z d c := by
  have hK := curvatureFirstBound_nonneg hG hd
  have hF := flowCoordinateBound_nonneg (heightQuotientJetBound_nonneg hG hZ hd hc)
  unfold heightCapCurvatureBound
  positivity

theorem heightCapCoefficientBound_dominates {G Z d c e0 : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0) (ell : ℕ) :
    0 ≤ heightCapCoefficientBound G Z d c e0 ell ∧
    heightAJetBound G Z d c ≤ heightCapCoefficientBound G Z d c e0 ell ∧
    2*heightBJetBound G Z d c ell ≤ heightCapCoefficientBound G Z d c e0 ell ∧
    heightBJetBound G Z d c ell ≤ heightCapCoefficientBound G Z d c e0 ell ∧
    heightCapCValueBound G Z d c e0 ell ≤ heightCapCoefficientBound G Z d c e0 ell := by
  have hA := heightAJetBound_nonneg hG hZ hd hc
  have hB := heightBJetBound_nonneg hG hZ hd hc ell
  have hr := heightRemainderBound_nonneg hG hZ hd hc he0 ell
  have hC : 0 ≤ heightCapCValueBound G Z d c e0 ell := by
    unfold heightCapCValueBound
    positivity
  unfold heightCapCoefficientBound
  constructor
  · positivity
  constructor
  · linarith only [hB,hC]
  constructor
  · linarith only [hA,hC]
  constructor
  · linarith only [hA,hB,hC]
  · linarith only [hA,hB]

theorem heightChartC_value_bound
    {g : MetricField} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ} {G Z d c e0 : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0) (ell : ℕ)
    (hAB : CoordinateBound (heightChartA g z Y) capChartDomain 1 (heightAJetBound G Z d c))
    (hrB : ∀ p ∈ capChartDomain,
      |heightChartRemainder g z Y ell p| ≤ heightRemainderBound G Z d c e0 ell ∧
      heightChartC g z Y ell p = ((ell : ℝ)+1)*coordPartial 1 (heightChartA g z Y) p +
        heightChartA g z Y p*heightChartRemainder g z Y ell p)
    {p : Coord} (hp : p ∈ capChartDomain) :
    |heightChartC g z Y ell p| ≤ heightCapCValueBound G Z d c e0 ell := by
  have hel : 0 ≤ (ell : ℝ)+1 := by positivity
  have hfirst := mul_le_mul_of_nonneg_left (hAB [1] (by norm_num) p hp) hel
  have hsecond :=
    (mul_le_mul_of_nonneg_left (hrB p hp).1 (abs_nonneg (heightChartA g z Y p))).trans
      (mul_le_mul_of_nonneg_right (hAB [] (by norm_num) p hp)
        (heightRemainderBound_nonneg hG hZ hd hc he0 ell))
  rw [(hrB p hp).2]
  calc
    _ ≤ |((ell : ℝ)+1)*coordPartial 1 (heightChartA g z Y) p| +
        |heightChartA g z Y p*heightChartRemainder g z Y ell p| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul,abs_of_nonneg hel,abs_mul]
      exact add_le_add hfirst hsecond

theorem heightChartB_primitive_first_bounds
    {g : MetricField} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ} {MB : ℝ} (ell : ℕ)
    (hMB : 0 ≤ MB) (hB : ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain)
    (hBB : CoordinateBound (heightChartB g z Y ell) capChartDomain 1 MB)
    {p : Coord} (hp : p ∈ capChartDomain) :
    |coordinatePrimitive (heightChartB g z Y ell) p| ≤ 2*MB ∧
      ∀ i : Fin 2, |coordPartial i (coordinatePrimitive (heightChartB g z Y ell)) p| ≤ 2*MB := by
  obtain ⟨hIv,hIs⟩ := heightChartB_primitive_bounds ell hB hBB hp
  refine ⟨hIv,?_⟩
  intro i
  fin_cases i
  · simp only [Fin.mk_zero]
    rw [coordinatePrimitive_partial_t hB (by norm_num : (0 : ℝ) < 2) hp]
    exact (hBB [] (by norm_num) p hp).trans (by linarith only [hMB])
  · simpa only [Fin.mk_one] using hIs

theorem heightCurvaturePullback_bound_one
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
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ)/100)
    (hrho : ∀ p ∈ capChartDomain, 1/Real.exp (2*heightQuotientJetBound G Z d c) ≤ capChartRho Y p) :
    CoordinateBound (capPullback Y (gaussianCurvature g)) capChartDomain 1 (heightCapCurvatureBound G Z d c) := by
  have hM := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hM
  have hK := curvatureFirstBound_nonneg hG hd
  exact capPullback_bound_one_from_partials hY (gaussianCurvature_contDiffOn hg hU) hU
    (fun p hp => hSU (hmapS hp)) hmapS hK hF
    (gaussianCurvature_coordinate_bound_one_closed hg hU hSU hG hd hgB hdet)
    (fun i p hp => capFlowHeight_partial_bound_of_rho hY hvar hode hmapS hsmall hM hrho hp i)

end SmoothLocal.Flow

end

end OAI
