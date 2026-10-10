import OAI.Geometry.IsometricImmersion.Energy.HeightEnergyJetBounds
import OAI.Geometry.IsometricImmersion.Curvature.CurvatureFirstBounds

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

def heightQuotientJetBound (G Z d c : ℝ) : ℝ :=
  LowQuotient.boundThroughThree (hessianJetBound G Z d) c
def heightAlongDJetBound (G Z d c : ℝ) : ℝ :=
  christoffelJetBound G d + 16 * heightQuotientJetBound G Z d c * christoffelJetBound G d +
    64 * (heightQuotientJetBound G Z d c)^2 * christoffelJetBound G d
def heightEnergyFirstQuotientBound (G Z d c : ℝ) : ℝ :=
  LowQuotient.boundThroughThree (32 * G * Z + hessianJetBound G Z d) c
def heightPFirstBound (G Z d c : ℝ) : ℝ :=
  heightAlongDJetBound G Z d c + 2 * curvatureFirstBound G d *
    (heightEnergyFirstQuotientBound G Z d c + 8 * darbouxGJetBound G Z d c * christoffelJetBound G d)

theorem heightQuotientJetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightQuotientJetBound G Z d c := by
  obtain ⟨h0, h1, h2, h3⟩ := LowQuotient.bounds_nonneg (hessianJetBound_nonneg hG hZ hd) hc
  dsimp [heightQuotientJetBound, LowQuotient.boundThroughThree]
  positivity

theorem heightAlongDJetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightAlongDJetBound G Z d c := by
  have hq := heightQuotientJetBound_nonneg hG hZ hd hc
  have hΓ := christoffelJetBound_nonneg hG hd
  dsimp [heightAlongDJetBound]; positivity

theorem heightEnergyFirstQuotientBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightEnergyFirstQuotientBound G Z d c := by
  have hH := hessianJetBound_nonneg hG hZ hd
  obtain ⟨h0, h1, h2, h3⟩ := LowQuotient.bounds_nonneg (show 0 ≤ 32 * G * Z + hessianJetBound G Z d by positivity) hc
  dsimp [heightEnergyFirstQuotientBound, LowQuotient.boundThroughThree]
  positivity

theorem heightPFirstBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) : 0 ≤ heightPFirstBound G Z d c := by
  have hA := heightAlongDJetBound_nonneg hG hZ hd hc
  have hK := curvatureFirstBound_nonneg hG hd
  have hJ := heightEnergyFirstQuotientBound_nonneg hG hZ hd hc
  have hD := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hΓ := christoffelJetBound_nonneg hG hd
  dsimp [heightPFirstBound]; positivity

theorem height_jetEnergy_first_coordinate_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G)
    (hzB : CoordinateBound z U 4 Z) (i : Fin 2) :
    CoordinateBound (fun p => coordPartial i (jetEnergy g p) (fun r => coordPartial r z p)) U 3
      (32 * G * Z) := by
  have hzS (j : Fin 2) := partial_contDiffOn hz hU j
  have hzD (j : Fin 2) : CoordinateBound (coordPartial j z) U 3 Z := hzB.partial_bound j
  have hdiag (a j : Fin 2) := CoordinateBound.const_mul
    ((hg.1 a a).mul (hzS j)) hU
    (CoordinateBound.mul_through_three (hg.1 a a) (hzS j) hU hG hZ (hgB a a) (hzD j)) (2 : ℝ)
  have hoff (j : Fin 2) := CoordinateBound.mul_through_three
    ((hg.1 0 1).add (hg.1 1 0)) (hzS j) hU (by positivity : 0 ≤ G + G) hZ
    (CoordinateBound.add (hg.1 0 1) (hg.1 1 0) hU (hgB 0 1) (hgB 1 0)) (hzD j)
  fin_cases i
  · have hb := CoordinateBound.sub (((hg.1 0 1).add (hg.1 1 0)).mul (hzS 1))
      (contDiffOn_const.mul ((hg.1 1 1).mul (hzS 0))) hU (hoff 1) (hdiag 1 0)
    have hc : 8 * (G + G) * Z + |(2 : ℝ)| * (8 * G * Z) = 32 * G * Z := by norm_num; ring
    rw [hc] at hb
    apply CoordinateBound.congr_on hU hb
    intro p hp
    change coordPartial 0 (jetEnergy g p) (fun r => coordPartial r z p) =
      (g p 0 1 + g p 1 0) * coordPartial 1 z p - 2 * (g p 1 1 * coordPartial 0 z p)
    rw [coordPartial_jetEnergy]
    norm_num
    ring
  · have hb := CoordinateBound.sub (((hg.1 0 1).add (hg.1 1 0)).mul (hzS 0))
      (contDiffOn_const.mul ((hg.1 0 0).mul (hzS 1))) hU (hoff 0) (hdiag 0 1)
    have hc : 8 * (G + G) * Z + |(2 : ℝ)| * (8 * G * Z) = 32 * G * Z := by norm_num; ring
    rw [hc] at hb
    apply CoordinateBound.congr_on hU hb
    intro p hp
    change coordPartial 1 (jetEnergy g p) (fun r => coordPartial r z p) =
      (g p 0 1 + g p 1 0) * coordPartial 0 z p - 2 * (g p 0 0 * coordPartial 1 z p)
    rw [coordPartial_jetEnergy]
    norm_num
    ring

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

theorem height_christoffelAlongD_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) (i : Fin 2) :
    CoordinateBound (fun p => christoffelAlongD g p (hessianQuotient g z p) i) U 3
      (heightAlongDJetBound G Z d c) := by
  obtain ⟨hqs, hqb⟩ := hessianQuotient_bound_from_metric_height_jets hg hU hz hG hZ hd hc hgB hzB hdet hyy
  have hqN := heightQuotientJetBound_nonneg hG hZ hd hc
  have hΓN := christoffelJetBound_nonneg hG hd
  have hΓs (a b : Fin 2) := christoffel_contDiffOn hg hU i a b
  have hΓb (a b : Fin 2) := christoffel_coordinate_bound hg hU hG hd hgB hdet i a b
  have hqb' : CoordinateBound (hessianQuotient g z) U 3 (heightQuotientJetBound G Z d c) := hqb
  have hqΓ := CoordinateBound.mul_through_three hqs (hΓs 0 1) hU hqN hΓN hqb' (hΓb 0 1)
  have htwice := CoordinateBound.const_mul (hqs.mul (hΓs 0 1)) hU hqΓ (2 : ℝ)
  have hqsq : CoordinateBound (fun p => (hessianQuotient g z p)^2) U 3
      (8 * (heightQuotientJetBound G Z d c)^2) := by
    convert CoordinateBound.mul_through_three hqs hqs hU hqN hqN hqb' hqb' using 1 <;>
      simp only [pow_two, mul_assoc]
  have hthird := CoordinateBound.mul_through_three (hqs.pow 2) (hΓs 1 1) hU
    (by positivity : 0 ≤ 8 * (heightQuotientJetBound G Z d c)^2) hΓN hqsq (hΓb 1 1)
  have hb := CoordinateBound.add
    ((hΓs 0 0).sub (contDiffOn_const.mul (hqs.mul (hΓs 0 1))))
    ((hqs.pow 2).mul (hΓs 1 1)) hU
    (CoordinateBound.sub (hΓs 0 0) (contDiffOn_const.mul (hqs.mul (hΓs 0 1))) hU (hΓb 0 0) htwice) hthird
  have hconstant : christoffelJetBound G d + |(2 : ℝ)| *
      (8 * heightQuotientJetBound G Z d c * christoffelJetBound G d) +
      8 * (8 * (heightQuotientJetBound G Z d c)^2) * christoffelJetBound G d =
      heightAlongDJetBound G Z d c := by norm_num [heightAlongDJetBound]; ring
  rw [hconstant] at hb
  apply CoordinateBound.congr_on hU hb
  intro p hp
  change christoffelAlongD g p (hessianQuotient g z p) i =
    christoffel g i 0 0 p - 2 * (hessianQuotient g z p * christoffel g i 0 1 p) +
      (hessianQuotient g z p)^2 * christoffel g i 1 1 p
  rw [christoffelAlongD_eq hg hU hp]
  ring

theorem heightPFirst_coordinate_bound_one
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) (i : Fin 2) :
    CoordinateBound (heightPFirst g z i) U 1 (heightPFirstBound G Z d c) := by
  have hne := LowQuotient.denominator_ne_zero hc hyy
  have hH := hessianJetBound_nonneg hG hZ hd
  have hΓ := christoffelJetBound_nonneg hG hd
  have hD := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hJ := heightEnergyFirstQuotientBound_nonneg hG hZ hd hc
  have hK := curvatureFirstBound_nonneg hG hd
  have hsH := covHessian_contDiffOn hg hU hz 1 1
  have hsJ := height_jetEnergy_first_contDiffOn hg hU hz i
  have hsG := darbouxG_contDiffOn hg hU hz hne
  have hsΓ := christoffel_contDiffOn hg hU i 1 1
  have hJB := height_jetEnergy_first_coordinate_bound hg hU hz hG hZ
    (fun a b => (hgB a b).mono (by norm_num) le_rfl) (hzB.mono (by norm_num) le_rfl) i
  have hHB := covHessian_coordinate_bound hg hU hz hG hZ hd hgB hzB hdet 1 1
  let N := 32 * G * Z + hessianJetBound G Z d
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hJN : 32 * G * Z ≤ N := by dsimp [N]; linarith
  have hHN : hessianJetBound G Z d ≤ N := by dsimp [N]; nlinarith [mul_nonneg hG hZ]
  have hdiv : CoordinateBound (fun p => coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) /
      covHessian g z p 1 1) U 3 (heightEnergyFirstQuotientBound G Z d c) := by
    intro ds hds p hp
    exact LowQuotient.quotient_bound_through_three hsJ hsH hU hN hc
      (hJB.mono le_rfl hJN) (hHB.mono le_rfl hHN) hyy ds hds hp
  have hGΓ := CoordinateBound.mul_through_three hsG hsΓ hU hD hΓ
    (darbouxG_coordinate_bound hg hU hz hG hZ hd hc hgB hzB hdet hyy)
    (christoffel_coordinate_bound hg hU hG hd hgB hdet i 1 1)
  have hsdiv := hsJ.div hsH hne
  have hbracket := CoordinateBound.add hsdiv (hsG.mul hsΓ) hU hdiv hGΓ
  have hmul := CoordinateBound.mul_through_one (gaussianCurvature_contDiffOn hg hU)
    (hsdiv.add (hsG.mul hsΓ)) hU hK
    (by positivity : 0 ≤ heightEnergyFirstQuotientBound G Z d c + 8 * darbouxGJetBound G Z d c * christoffelJetBound G d)
    (gaussianCurvature_coordinate_bound_one hg hU hG hd hgB hdet)
    (hbracket.mono (by norm_num) le_rfl)
  have hbs := height_christoffelAlongD_contDiffOn hg hU hz hne i
  have hb := CoordinateBound.add hbs ((gaussianCurvature_contDiffOn hg hU).mul (hsdiv.add (hsG.mul hsΓ))) hU
    ((height_christoffelAlongD_coordinate_bound hg hU hz hG hZ hd hc hgB hzB hdet hyy i).mono
      (by norm_num) le_rfl) hmul
  apply CoordinateBound.congr_on hU hb
  intro p hp
  change heightPFirst g z i p = christoffelAlongD g p (hessianQuotient g z p) i +
    gaussianCurvature g p *
      (coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) / covHessian g z p 1 1 +
        darbouxG g z p * christoffel g i 1 1 p)
  rw [heightPFirst_eq hg hU hp (hne p hp) i]
  unfold darbouxG
  simp only [div_eq_mul_inv]
  ring

end SmoothLocal.Geometry

end

end OAI
