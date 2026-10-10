import OAI.Geometry.IsometricImmersion.Calculus.HessianJetBounds
import OAI.Geometry.IsometricImmersion.Immersions.HeightCoefficientRegularity
import OAI.Geometry.IsometricImmersion.Coordinates.CoordinateFirstBounds

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

def heightEnergyJetBound (G Z : ℝ) : ℝ := 16 * G^2 + 256 * G * Z^2
def darbouxGJetBound (G Z d c : ℝ) : ℝ :=
  LowQuotient.boundThroughThree
    (heightEnergyJetBound G Z + 8 * (hessianJetBound G Z d)^2) (c^2)

theorem heightEnergyJetBound_nonneg {G Z : ℝ} (hG : 0 ≤ G) : 0 ≤ heightEnergyJetBound G Z := by
  dsimp [heightEnergyJetBound]; positivity

theorem darbouxGJetBound_nonneg {G Z d c : ℝ} (hG : 0 ≤ G) (hc : 0 < c) :
    0 ≤ darbouxGJetBound G Z d c := by
  have hE := heightEnergyJetBound_nonneg (Z := Z) hG
  obtain ⟨h0, h1, h2, h3⟩ := LowQuotient.bounds_nonneg
    (show 0 ≤ heightEnergyJetBound G Z + 8 * (hessianJetBound G Z d)^2 by positivity) (pow_pos hc 2)
  dsimp [darbouxGJetBound, LowQuotient.boundThroughThree]
  positivity

theorem heightEnergy_coordinate_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G)
    (hzB : CoordinateBound z U 4 Z) :
    CoordinateBound (heightEnergy g z) U 3 (heightEnergyJetBound G Z) := by
  have hzi (i : Fin 2) := partial_contDiffOn hz hU i
  have hzBi (i : Fin 2) : CoordinateBound (coordPartial i z) U 3 Z := hzB.partial_bound i
  have hsquare (i : Fin 2) : CoordinateBound (fun p => (coordPartial i z p)^2) U 3 (8 * Z^2) := by
    convert CoordinateBound.mul_through_three (hzi i) (hzi i) hU hZ hZ (hzBi i) (hzBi i) using 1 <;>
      simp only [pow_two, mul_assoc]
  have hdiag0 := CoordinateBound.mul_through_three (hg.1 1 1) ((hzi 0).pow 2) hU hG
    (by positivity : 0 ≤ 8 * Z^2) (hgB 1 1) (hsquare 0)
  have hdiag1 := CoordinateBound.mul_through_three (hg.1 0 0) ((hzi 1).pow 2) hU hG
    (by positivity : 0 ≤ 8 * Z^2) (hgB 0 0) (hsquare 1)
  have hsum := CoordinateBound.add (hg.1 0 1) (hg.1 1 0) hU (hgB 0 1) (hgB 1 0)
  have hcross1 := CoordinateBound.mul_through_three ((hg.1 0 1).add (hg.1 1 0))
    (hzi 0) hU (by positivity : 0 ≤ G + G) hZ hsum (hzBi 0)
  have hcross := CoordinateBound.mul_through_three
    (((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)) (hzi 1) hU
    (by positivity : 0 ≤ 8 * (G + G) * Z) hZ hcross1 (hzBi 1)
  have hinner := CoordinateBound.add
    (((hg.1 1 1).mul ((hzi 0).pow 2)).sub ((((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)).mul (hzi 1)))
    ((hg.1 0 0).mul ((hzi 1).pow 2)) hU
    (CoordinateBound.sub ((hg.1 1 1).mul ((hzi 0).pow 2))
      ((((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)).mul (hzi 1)) hU hdiag0 hcross) hdiag1
  have hfull := CoordinateBound.sub (metricDet_contDiffOn hg)
    ((((hg.1 1 1).mul ((hzi 0).pow 2)).sub
      ((((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)).mul (hzi 1))).add
        ((hg.1 0 0).mul ((hzi 1).pow 2))) hU (metricDet_coordinate_bound hg hU hG hgB) hinner
  have hc : 16 * G^2 + (8 * G * (8 * Z^2) + 8 * (8 * (G + G) * Z) * Z + 8 * G * (8 * Z^2)) =
      heightEnergyJetBound G Z := by dsimp [heightEnergyJetBound]; ring
  rw [hc] at hfull
  exact CoordinateBound.congr_on hU hfull (fun p hp => heightEnergy_polynomial z hg hp)

theorem darbouxG_coordinate_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) :
    CoordinateBound (darbouxG g z) U 3 (darbouxGJetBound G Z d c) := by
  have hH := hessianJetBound_nonneg hG hZ hd
  have hE := heightEnergyJetBound_nonneg (Z := Z) hG
  have hh := covHessian_contDiffOn hg hU hz 1 1
  have hhB := covHessian_coordinate_bound hg hU hz hG hZ hd hgB hzB hdet 1 1
  have hhsq : CoordinateBound (fun p => (covHessian g z p 1 1)^2) U 3
      (8 * (hessianJetBound G Z d)^2) := by
    convert CoordinateBound.mul_through_three hh hh hU hH hH hhB hhB using 1 <;>
      simp only [pow_two, mul_assoc]
  have hEB := heightEnergy_coordinate_bound hg hU hz hG hZ
    (fun i j => (hgB i j).mono (by norm_num) le_rfl) (hzB.mono (by norm_num) le_rfl)
  let N := heightEnergyJetBound G Z + 8 * (hessianJetBound G Z d)^2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hn : heightEnergyJetBound G Z ≤ N := by dsimp [N]; nlinarith [sq_nonneg (hessianJetBound G Z d)]
  have hb : 8 * (hessianJetBound G Z d)^2 ≤ N := by dsimp [N]; linarith
  have hden (p : Coord) (hp : p ∈ U) : c^2 ≤ |(covHessian g z p 1 1)^2| := by
    rw [abs_pow]
    exact pow_le_pow_left₀ hc.le (hyy p hp) 2
  intro ds hds p hp
  exact LowQuotient.quotient_bound_through_three (heightEnergy_contDiffOn hg hU hz)
    (hh.pow 2) hU hN (pow_pos hc 2) (hEB.mono le_rfl hn) (hhsq.mono le_rfl hb) hden ds hds hp

theorem darbouxG_lower_of_energy_floor
    (g : MetricField) (z : Coord → ℝ) (p : Coord) {e0 H : ℝ}
    (he0 : 0 < e0) (hE : e0 ≤ heightEnergy g z p) (hH : 0 ≤ H)
    (hupper : |covHessian g z p 1 1| ≤ H) (hne : covHessian g z p 1 1 ≠ 0) :
    e0 / (1 + H)^2 ≤ darbouxG g z p := by
  have hsq : (covHessian g z p 1 1)^2 ≤ (1 + H)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (covHessian g z p 1 1))
      (hupper.trans (by linarith : H ≤ 1 + H)) 2
    simpa only [sq_abs] using hh
  have hl : 0 ≤ e0 / (1 + H)^2 := by positivity
  have heq : e0 / (1 + H)^2 * (1 + H)^2 = e0 :=
    div_mul_cancel₀ _ (pow_ne_zero 2 (by linarith : (1 : ℝ) + H ≠ 0))
  unfold darbouxG
  apply (le_div_iff₀ (sq_pos_of_ne_zero hne)).mpr
  calc
    _ ≤ e0 / (1 + H)^2 * (1 + H)^2 := mul_le_mul_of_nonneg_left hsq hl
    _ = e0 := heq
    _ ≤ heightEnergy g z p := hE

end SmoothLocal.Geometry

end

end OAI
