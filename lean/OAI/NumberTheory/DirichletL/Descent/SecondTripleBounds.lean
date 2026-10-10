import OAI.NumberTheory.DirichletL.Descent.SecondPunctureBudget

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0)

include hp in

theorem actual_second_common_center
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (Z g theta eta : ℝ) (hZ : 1 < Z)
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    -2*eta ≤ g-theta := by
  have hh : Z^(theta-eta) ≤ Z^(g+eta) :=
    hD.trans ((primeProductNorm_mono p hp hE).trans hG)
  have hh' := (Real.rpow_le_rpow_left_iff hZ).mp hh
  linarith

include hp in

theorem actual_second_label_center
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Z ell j eta : ℝ) (hZ : 1 < Z)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hJ : Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    j ≤ 2*ell+3*eta := by
  have hb := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos (Z^(ell+eta))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le h1 h2).1
  have hh := hJ.trans hb
  rw [←Real.rpow_mul_natCast (zero_lt_one.trans hZ).le] at hh
  have hh' := (Real.rpow_le_rpow_left_iff hZ).mp hh
  norm_num at hh'
  linarith

variable [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_second_q0_power_bound
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (Z ell R j eta : ℝ) (hZ : 0 < Z)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hactive : primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(R+eta))
    (hJ : Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) ≤ Z^(ell+R/2-j+5*eta/2) := by
  have hb := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos (Z^(ell+eta))
      (Real.rpow_pos_of_pos hZ _).le h1 h2).2.2
  have ha : ‖eisEmbedding (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤
      Z^((R+eta)/2) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.rpow_pos_of_pos hZ _).le).mp
    rw [←Real.rpow_mul_natCast hZ.le]
    norm_num
    simpa only [primeProductNorm,map_prod,norm_prod] using hactive
  change (Ideal.absNorm (Ideal.span {b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) : ℝ) ≤ _
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]
  apply hb.trans
  calc
    _ ≤ (Z^(ell+eta)*Z^((R+eta)/2))/Z^(j-eta) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left ha (by positivity))
        (Real.rpow_pos_of_pos hZ _) hJ
    _ = Z^((ell+eta)+(R+eta)/2-(j-eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_sub hZ]
    _ = _ := by congr 1; ring

end
end SevenEighths.InverseMoment

end OAI
