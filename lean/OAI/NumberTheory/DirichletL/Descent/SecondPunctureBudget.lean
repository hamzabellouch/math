import OAI.NumberTheory.DirichletL.Descent.SecondPuncture

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_residual_norm_eq_div (E G : Finset ι) (hE : E ⊆ G) :
    primeProductNorm p (G\E) = primeProductNorm p G/primeProductNorm p E := by
  have he : primeProductNorm p G = primeProductNorm p E*primeProductNorm p (G\E) := by
    rw [←primeProductNorm_union p E (G\E) Finset.disjoint_sdiff,Finset.union_sdiff_of_subset hE]
  rw [he]
  field_simp [(primeProductNorm_pos p hp E).ne']

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_residual_norm_power_bound (E G : Finset ι) (hE : E ⊆ G)
    (Z g theta eta : ℝ) (hZ : 0 < Z)
    (hg : primeProductNorm p G ≤ Z^(g+eta))
    (hd : Z^(theta-eta) ≤ primeProductNorm p E) :
    primeProductNorm p (G\E) ≤ Z^(g-theta+2*eta) := by
  rw [second_residual_norm_eq_div p hp E G hE]
  calc
    _ ≤ Z^(g+eta)/Z^(theta-eta) := div_le_div₀ (Real.rpow_pos_of_pos hZ _).le hg
      (Real.rpow_pos_of_pos hZ _) hd
    _ = Z^((g+eta)-(theta-eta)) := (Real.rpow_sub hZ _ _).symm
    _ = _ := by congr 1; ring

include hp in

theorem actual_second_puncture_power_budget
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 0 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (hB : primeProductNorm p x.cube.support ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      Z^(Q+ell+t+g-theta+4*eta) := by
  have hr := second_residual_norm_power_bound p hp _ _ hE Z g theta eta hZ hG hD
  apply (actual_second_inherited_puncture_norm p hp hpr x hE ht u v m hm).trans
  calc
    _ ≤ (Z^Q*Z^(t+eta))*Z^(ell+eta)*Z^(g-theta+2*eta) := by
      have hb0 := (primeProductNorm_pos p hp x.cube.support).le
      have hr0 := (primeProductNorm_pos p hp (x.second.sourceCommon\x.second.divisor)).le
      gcongr
    _ = Z^((Q+(t+eta))+(ell+eta)+(g-theta+2*eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by congr 1; ring

end
end SevenEighths.InverseMoment

end OAI
