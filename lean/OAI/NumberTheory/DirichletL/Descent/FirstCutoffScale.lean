import OAI.NumberTheory.DirichletL.Descent.FirstRowGeometry

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem first_physical_row_scale_bound
    (Z M r ell V delta B j eta tau dn cn jn : ℝ) (hZ : 0<Z)
    (_hdn : 0≤dn) (hcn : 0<cn) (_hjn : 0<jn)
    (hd : dn≤Z^(delta+eta)) (hc : Z^(B-eta)≤cn) (hj : Z^(j-eta)≤jn) :
    Z^tau*(Z^(r+eta))^2*(Z^(ell+eta))^4*(Z^(V+eta))^2*dn /
      (Z^M*cn^2*jn) ≤ Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau) := by
  have hpow (x : ℝ) (n : ℕ) : (Z^x)^n=Z^(x*n) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  calc
    _ ≤ Z^tau*(Z^(r+eta))^2*(Z^(ell+eta))^4*(Z^(V+eta))^2*Z^(delta+eta) /
        (Z^M*(Z^(B-eta))^2*Z^(j-eta)) := by
      apply div_le_div₀ (by positivity)
      · exact mul_le_mul_of_nonneg_left hd (by positivity)
      · positivity
      · exact mul_le_mul (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.rpow_pos_of_pos hZ _).le hc 2) (Real.rpow_pos_of_pos hZ _).le)
          hj (Real.rpow_pos_of_pos hZ _).le (by positivity)
    _ = _ := by
      simp only [hpow,←Real.rpow_add hZ,←Real.rpow_sub hZ]
      congr 1
      unfold firstPhysicalHeight
      norm_num
      ring

theorem first_ratio_canonical_row {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (S N Q : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i)
    (hNQ : Disjoint N Q) (hNS : Disjoint N S) (hQS : Disjoint Q S)
    (common divisor : Finset ι) (f : Ideal O) (h : O)
    (Z M r ell V delta B j eta tau : ℝ) (hZ : 0<Z)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤Z^(ell+eta))
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤Z^(ell+eta))
    (hf : (Ideal.absNorm f : ℝ)≤Z^(V+eta))
    (hd : primeProductNorm p divisor≤Z^(delta+eta))
    (hc : Z^(B-eta)≤primeProductNorm p common)
    (hj : Z^(j-eta)≤‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2)
    (hcol₁ : ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p N≤Z^(r+eta))
    (hcol₂ : ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p Q≤Z^(r+eta))
    (hratio : (Z^M/(primeProductNorm p divisor *
      primeProductNorm p ((N∪Q)∪cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂)))*‖eisEmbedding h‖^2≤Z^tau) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂) (f,h))‖^2 ≤
      Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau) := by
  have hrow := first_ratio_actual_row p hp S N Q v₁ v₂ ε₁ ε₂ hv hNQ hNS hQS common divisor f h
    (Z^M) (Z^tau) (Z^(r+eta)) (Z^(ell+eta)) (Z^(V+eta))
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hb₁ hb₂ hf hcol₁ hcol₂ hratio
  exact hrow.trans (first_physical_row_scale_bound Z M r ell V delta B j eta tau
    (primeProductNorm p divisor) (primeProductNorm p common)
    (‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2) hZ
    (primeProductNorm_pos p hp _).le (primeProductNorm_pos p hp _)
    (SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)) hd hc hj)

end
end SevenEighths.InverseMoment

end OAI
