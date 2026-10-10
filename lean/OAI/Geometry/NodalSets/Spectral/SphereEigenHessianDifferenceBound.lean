import OAI.Geometry.NodalSets.Elliptic.RealCommutatorDerivativeBound
import OAI.Geometry.NodalSets.Elliptic.RealCompactL2MapLemmas
import OAI.Geometry.NodalSets.Elliptic.RealFinitePositiveBounds
import OAI.Geometry.NodalSets.Elliptic.RealHessianDifferenceCutoffsLemmas
import OAI.Geometry.NodalSets.Elliptic.RealWeightedLocalDifferenceBound
import OAI.Geometry.NodalSets.Spectral.SphereEigenForcingDerivativeBound
import OAI.Geometry.NodalSets.Spectral.SphereEigenHessianLocalizedEnergy

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_eigen_hessian_difference_bound (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) :
    ∃ C1 > 0, ∃ C > 0, ∀ (f : SphereWeightedL2 d), sphereL2Resolvent d f=mu • f →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))),
        (∑ a, ∑ j, ‖H a j‖^2) ≤ C1*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ a j psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          (∫ x in Yau.realCenteredCube 4 (1/2),
            (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x j) =
            -(∫ x in Yau.realCenteredCube 4 (1/2), H a j x*psi x)) ∧
        ∀ (k i : Fin 4) (h : ℝ), |h| ≤ 1/32 →
          (∀ a, MemLp (Yau.realDifferenceQuotient i h (H k a)) 2
            (volume.restrict (Yau.realCenteredCube 4 (1/4)))) ∧
          (∑ a, ∫ x in Yau.realCenteredCube 4 (1/4), (Yau.realDifferenceQuotient i h (H k a) x)^2) ≤
            C*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  obtain ⟨C1,hC1,m,hm,K,hK,henergy⟩ := sphere_eigen_hessian_localized_energy d p hrho
  obtain ⟨eta,chi,he,hchi,hec,hchic,hes,hchis,heb,hchib,he1,hend⟩ := Yau.real_hessian_difference_cutoffs
  let Q := Yau.realCenteredCube 4 (1/2)
  let Q0 := Yau.realCenteredCube 4 (1/4)
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/2)
  have hQ0 : IsCompact Q0 := Yau.realCenteredCube_isCompact 4 (1/4)
  have hcs : tsupport chi ⊆ Q := hchis.trans interior_subset
  have hetab (x : Yau.Jets.Coord) : |eta x| ≤ 1 := by rw [abs_of_nonneg (heb x).1]; exact (heb x).2
  have hends (i : Fin 4) (h : ℝ) (hh : |h| ≤ 1/32) (x : Yau.Jets.Coord) (hx : x ∈ tsupport eta) :
      x ∈ Q ∧ x+Pi.single i h ∈ Q ∧ chi x=1 ∧ chi (x+Pi.single i h)=1 := by
    have ht := hend i h hh x hx
    exact ⟨interior_subset ht.1,interior_subset ht.2.1,ht.2.2.1.eq_of_nhds,ht.2.2.2.eq_of_nhds⟩
  obtain ⟨D,hD,hUb⟩ := sphere_half_cube_gradient_bound d p
  obtain ⟨CW,hCW,hWb⟩ := Yau.real_indicator_weighted_bound hQ eta he.continuous
  choose CF hCF hFb using fun k ↦ sphere_eigen_forcing_derivative_bound d p hrho mu k
  obtain ⟨F0,hF0,hFmax⟩ := Yau.real_finite_positive_majorant CF
  choose CG hCG hGb using fun k j i ↦ Yau.real_localized_commutator_derivative_bound hQ
    (sphereChartPrincipalDensity d p) (sphereChartPrincipalDensity_smooth d p) chi hchi hcs k j i
  obtain ⟨G0,hG0,hGmax⟩ := Yau.real_finite_positive_majorant
    (fun t : Fin 4 × Fin 4 × Fin 4 ↦ CG t.1 t.2.1 t.2.2)
  choose CR hCR hRb using fun i a ↦ Yau.real_weighted_local_difference_bound hQ
    (fun x ↦ Yau.coordPartial eta x a) chi (Yau.real_coordPartial_smooth eta he a).continuous
    (hec.fderiv_apply ℝ (Pi.single a 1)) hchi hcs i
  obtain ⟨R0,hR0,hRmax⟩ := Yau.real_finite_positive_majorant (fun t : Fin 4 × Fin 4 ↦ CR t.1 t.2)
  let C := (4/m)*((16/m)*(F0+4*G0*(4*D+C1))+K*CW*C1+(K+m)*4*R0*(D+C1))
  refine ⟨C1,hC1,C,by dsimp [C]; positivity,fun f heigen ↦ ?_⟩
  obtain ⟨H,hbound,hweak,hweighted⟩ := henergy mu hmu f heigen
  refine ⟨H,hbound,hweak,fun k i h hh ↦ ?_⟩
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let U := fun a ↦ (sphereChartDerivativeMap d p a (sphereWeakSolution d f) : Yau.Jets.Coord → ℝ)
  let V := fun a ↦ Q.indicator (H k a)
  let q := Yau.realDifferenceQuotient i h (Q.indicator (U k))
  let T := fun a x ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
  let W := fun a x ↦ eta x*V a x
  let R := fun a x ↦ Yau.coordPartial eta x a*q x
  let G := Yau.realWeakGradientCommutator (sphereChartPrincipalDensity d p) U k
  let DG := Yau.realWeakGradientCommutatorDerivative (sphereChartPrincipalDensity d p) U (fun a j ↦ H a j) k
  let F := Q.indicator (sphereEigenForcingDerivative d p mu f k)
  have hwt := hweighted k eta chi he hec hetab hes hchi hcs i h hh (hends i h hh)
  have hUn (a : Fin 4) : (∫ x in Q, (U a x)^2) ≤ D*E :=
    (hUb _ a).2.trans (mul_le_mul_of_nonneg_left (by dsimp [E]; nlinarith [sq_nonneg ‖f‖]) hD.le)
  have hUsum : (∑ a, ∫ x in Q, (U a x)^2) ≤ 4*D*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hUn a)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using ht
  have hHnorm (a j : Fin 4) : (∫ x in Q, (H a j x)^2)=‖H a j‖^2 := by
    symm
    simpa only [Lp.toLp_coeFn] using Yau.real_toLp_norm_sq _ (Lp.memLp (H a j))
  have hHrow (a : Fin 4) : (∑ j, ∫ x in Q, (H a j x)^2) ≤ C1*E := by
    simp_rw [hHnorm]
    exact (Finset.single_le_sum (f := fun b ↦ ∑ j, ‖H b j‖^2)
      (fun b _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg _)) (Finset.mem_univ a)).trans hbound
  have hHcol (j : Fin 4) : (∑ a, ∫ x in Q, (H a j x)^2) ≤ C1*E := by
    simp_rw [hHnorm]
    exact (Finset.sum_le_sum (fun a _ ↦ Finset.single_le_sum (f := fun l ↦ ‖H a l‖^2)
      (fun l _ ↦ sq_nonneg _) (Finset.mem_univ j))).trans hbound
  have hHone (a j : Fin 4) : (∫ x in Q, (H a j x)^2) ≤ C1*E :=
    (Finset.single_le_sum (f := fun l ↦ ∫ x in Q, (H a l x)^2)
      (fun l _ ↦ integral_nonneg (fun x ↦ sq_nonneg _)) (Finset.mem_univ j)).trans (hHrow a)
  have hWsum : (∑ a, ∫ x, (W a x)^2) ≤ CW*C1*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ (hWb (H k a) (Lp.memLp _)).2)
    simp only [← Finset.mul_sum] at ht
    exact ht.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hHrow k) hCW.le)
  have hRone (a : Fin 4) : (∫ x, (R a x)^2) ≤ R0*(D+C1)*E := by
    have ht := (hRb i a (U k) (H k i) (hUb _ k).1 (Lp.memLp _) (hweak k i) h
      (fun x hx ↦ hends i h hh x (tsupport_fderiv_apply_subset ℝ (Pi.single a 1) hx))).2
    have hb := (add_le_add (hUn k) (hHone k i))
    have hc := (mul_le_mul_of_nonneg_left hb (hCR i a).le)
    have hmax := mul_le_mul_of_nonneg_right (hRmax (i,a))
      (show 0 ≤ (D+C1)*E by positivity)
    have heq : D*E+C1*E=(D+C1)*E := by ring
    rw [heq] at hc
    exact ht.trans (hc.trans (by simpa only [mul_assoc] using hmax))
  have hRsum : (∑ a, ∫ x, (R a x)^2) ≤ 4*R0*(D+C1)*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hRone a)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using ht
  have hGone (j : Fin 4) : (∫ x, (chi x*DG j i x+Yau.coordPartial chi x i*G j x)^2) ≤
      G0*(4*D+C1)*E := by
    have ht := (hGb k j i U (fun a l ↦ H a l) (fun a ↦ (hUb _ a).1) (fun a l ↦ Lp.memLp _)).2
    have hb := mul_le_mul_of_nonneg_left (add_le_add hUsum (hHcol i)) (hCG k j i).le
    have heq : 4*D*E+C1*E=(4*D+C1)*E := by ring
    rw [heq] at hb
    have hmax := mul_le_mul_of_nonneg_right (hGmax (k,j,i))
      (show 0 ≤ (4*D+C1)*E by positivity)
    exact ht.trans (hb.trans (by simpa only [mul_assoc] using hmax))
  have hGsum : (∑ j, ∫ x, (chi x*DG j i x+Yau.coordPartial chi x i*G j x)^2) ≤
      4*G0*(4*D+C1)*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hGone j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using ht
  have hFint : (∫ x, (F x)^2) ≤ F0*E := by
    have hind : (fun x ↦ (F x)^2)=Q.indicator (fun x ↦ (sphereEigenForcingDerivative d p mu f k x)^2) := by
      funext x
      by_cases hx : x ∈ Q
      · simp only [F,indicator_of_mem hx]
      · simp only [F,indicator_of_notMem hx,zero_pow (by decide : (2:ℕ)≠0)]
    change (∫ x, (fun y ↦ (F y)^2) x) ≤ _
    rw [hind,integral_indicator hQ.measurableSet]
    exact (hFb k f).2.trans (mul_le_mul_of_nonneg_right (hFmax k) hE)
  have hglobal : (∑ a, ∫ x, (T a x)^2) ≤ C*E := by
    have ht := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add hFint hGsum) (show 0 ≤ 16/m by positivity))
      (mul_le_mul_of_nonneg_left hWsum hK.le))
      (mul_le_mul_of_nonneg_left hRsum (add_nonneg hK.le hm.le))
    have hb := hwt.2.trans (mul_le_mul_of_nonneg_left ht (show 0 ≤ 4/m by positivity))
    have hcform : (4/m)*((16/m)*(F0*E+4*G0*(4*D+C1)*E)+
        K*(CW*C1*E)+(K+m)*(4*R0*(D+C1)*E))=C*E := by
      dsimp [C]
      ring
    exact hb.trans_eq hcform
  have hident (a : Fin 4) (x : Yau.Jets.Coord) (hx : x ∈ Q0) :
      Yau.realDifferenceQuotient i h (H k a) x=T a x := by
    have hxQ : x ∈ Q := Yau.realCenteredCube_mono (by norm_num) hx
    have htQ : x+Pi.single i h ∈ Q := by
      apply Yau.realCenteredCube_shift i (h := -h) (r := 1/4)
        (by simpa only [abs_neg] using (show |h| ≤ (1/2:ℝ)-1/4 by linarith))
      simpa only [Pi.single_neg,add_neg_cancel_right] using hx
    dsimp [T,V]
    rw [(he1 x hx).eq_of_nhds,one_mul]
    simp only [Yau.realDifferenceQuotient,indicator_of_mem hxQ,indicator_of_mem htQ]
  refine ⟨fun a ↦ ?_,?_⟩
  · apply ((hwt.1 a).1.restrict Q0).ae_eq
    filter_upwards [ae_restrict_mem hQ0.measurableSet] with x hx
    exact (hident a x hx).symm
  · apply le_trans (Finset.sum_le_sum (fun a _ ↦ ?_)) hglobal
    have hEq : (∫ x in Q0, (Yau.realDifferenceQuotient i h (H k a) x)^2)=
        ∫ x in Q0, (T a x)^2 := by
      apply setIntegral_congr_fun hQ0.measurableSet
      intro x hx
      change (Yau.realDifferenceQuotient i h (H k a) x)^2=(T a x)^2
      rw [hident a x hx]
    rw [hEq]
    exact setIntegral_le_integral (hwt.1 a).1.integrable_sq
      (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))

end
end Yau.Target

end OAI
