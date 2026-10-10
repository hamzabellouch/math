import OAI.NumberTheory.DirichletL.Descent.FirstTailAbsorption

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} (p : ι→O) (hp : ∀i,p i≠0)

include hp in
theorem first_nonempty_column_center (U : Finset ι) (Z r eta : ℝ) (hZ : 1<Z)
    (hU : primeProductNorm p U≤Z^(r+eta)) : -eta≤r := by
  have hh : Z^(0:ℝ)≤Z^(r+eta) := by
    rw [Real.rpow_zero]
    exact (primeProductNorm_ge_one p hp U).trans hU
  have := (Real.rpow_le_rpow_left_iff hZ).mp hh
  linarith

variable [DecidableEq ι]

include hp in

theorem first_source_divisor_center (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z r ell delta eta : ℝ) (hZ : 1<Z)
    (h1 : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta))
    (hC : primeProductNorm p C≤Z^(r+eta))
    (hd : Z^(delta-eta)≤primeProductNorm p D) : delta≤r+2*ell+4*eta := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hh := hd.trans (cubeSourceDivisor_norm_bound p hp b C D (Z^(ell+eta)) (Z^(r+eta))
    (Real.rpow_pos_of_pos hz _).le (Real.rpow_pos_of_pos hz _).le hCB h1 h2 hC hD)
  rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz] at hh
  have := (Real.rpow_le_rpow_left_iff hZ).mp hh
  norm_num at this
  linarith

include hp in
theorem first_source_scalar_caps (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M Mmax Fmax r ell V eta : ℝ) (hZ : 1≤Z)
    (hM : 0≤M) (hMm : M≤Mmax) (hF : 0≤Fmax) (hell : 0≤ell) (hV : 0≤V)
    (heta : 0≤eta) (hr : -eta≤r) (hwhole : r+3*ell+V≤Fmax)
    (h1 : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta))
    (hC : primeProductNorm p C≤Z^(r+eta)) :
    let cap := Mmax+Fmax+3*eta
    Z^M≤Z^cap ∧ (Z^M)⁻¹≤Z^cap ∧ primeProductNorm p D≤Z^cap ∧
    primeProductNorm p (cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤Z^cap ∧
    (∀ eps : ι→Bool,Z^(r+eta)/(‖eisEmbedding (aLabel p b.support eps)‖^2*primeProductNorm p C)≤Z^cap) := by
  dsimp only
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hcap : 0≤Mmax+Fmax+3*eta := by linarith
  refine ⟨Real.rpow_le_rpow_of_exponent_le hZ (by linarith),?_,?_,?_,?_⟩
  · calc
      _ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow hZ hM)
      _ ≤ _ := Real.one_le_rpow hZ hcap
  · have hd := cubeSourceDivisor_norm_bound p hp b C D (Z^(ell+eta)) (Z^(r+eta))
      (Real.rpow_pos_of_pos hz _).le (Real.rpow_pos_of_pos hz _).le hCB h1 h2 hC hD
    apply hd.trans
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  · apply (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
    apply (cubeCoordinates_radical_bound p hp b (Z^(ell+eta)) (Real.rpow_pos_of_pos hz _).le h1 h2).trans
    rw [←Real.rpow_mul_natCast hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  · intro eps
    have ha := element_norm_ge_one (aLabel p b.support eps) (primeProduct_ne_zero p hp _ _)
    have hc := primeProductNorm_ge_one p hp C
    calc
      _ ≤ Z^(r+eta) := div_le_self (Real.rpow_pos_of_pos hz _).le (one_le_mul_of_one_le_of_one_le ha hc)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

end
end SevenEighths.InverseMoment

end OAI
