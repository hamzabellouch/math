import OAI.NumberTheory.DirichletL.Descent.FirstSourceSize
import OAI.NumberTheory.DirichletL.Descent.SecondCanonicalTail

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)

include hp in
theorem first_source_height_bounds (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M Mmax Fmax r ell V delta B j eta tau : ℝ) (hZ : 1<Z)
    (hM : 0≤M) (hMm : M≤Mmax) (hell : 0≤ell) (hV : 0≤V)
    (hdelta : 0≤delta) (hB : 0≤B) (hj : 0≤j) (heta : 0≤eta) (htau : 0≤tau)
    (hwhole : r+3*ell+V≤Fmax)
    (h1 : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta))
    (hC : primeProductNorm p C≤Z^(r+eta))
    (hc : Z^(B-eta)≤primeProductNorm p C)
    (hd : Z^(delta-eta)≤primeProductNorm p D)
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2) :
    -Mmax≤firstPhysicalHeight M r ell V delta B j+12*eta+tau ∧
    firstPhysicalHeight M r ell V delta B j+12*eta+tau≤3*Fmax+16*eta+tau := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hd' := first_source_divisor_center p hp b C D hCB hD Z r ell delta eta hZ h1 h2 hC hd
  have hb' := (Real.rpow_le_rpow_left_iff hZ).mp (hc.trans hC)
  have hj' := hJ.trans ((cube_label_norm_bounds p hp b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos (Z^(ell+eta)) (Real.rpow_pos_of_pos hz _).le h1 h2).1)
  rw [←Real.rpow_mul_natCast hz.le] at hj'
  have hj'' := (Real.rpow_le_rpow_left_iff hZ).mp hj'
  norm_num at hj''
  unfold firstPhysicalHeight
  constructor <;> linarith

include hp in

theorem second_source_scalar_caps (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M Mmax Fmax r ell V delta B j eta tau A t L : ℝ) (hZ : 1<Z)
    (hM : 0≤M) (hMm : M≤Mmax) (hFm : 0≤Fmax) (hell : 0≤ell) (hV : 0≤V)
    (hdelta : 0≤delta) (hB : 0≤B) (hj : 0≤j) (heta : 0≤eta) (htau : 0≤tau)
    (hA : 0≤A) (ht : 0≤t) (hwhole : r+3*ell+V≤Fmax)
    (h1 : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta))
    (hC : primeProductNorm p C≤Z^(r+eta))
    (hc : Z^(B-eta)≤primeProductNorm p C)
    (hd : Z^(delta-eta)≤primeProductNorm p D)
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2)
    (hL : L≤Z^(r-A-B-t+4*eta)) :
    let Y := Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)
    let cap := Mmax+3*Fmax+16*eta+tau
    Y≤Z^cap ∧ Y⁻¹≤Z^cap ∧ L≤Z^cap := by
  dsimp only
  have hz : 0<Z := zero_lt_one.trans hZ
  obtain ⟨hlo,hhi⟩ := first_source_height_bounds p hp b C D hCB hD
    Z M Mmax Fmax r ell V delta B j eta tau hZ hM hMm hell hV hdelta hB hj heta htau
    hwhole h1 h2 hC hc hd hJ
  refine ⟨Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith),?_,?_⟩
  · rw [←Real.rpow_neg hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · exact hL.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))

end
end SevenEighths.InverseMoment

end OAI
