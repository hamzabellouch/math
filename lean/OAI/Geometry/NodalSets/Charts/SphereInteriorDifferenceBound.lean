import OAI.Geometry.NodalSets.Charts.SphereInteriorLocalizedEnergy
import OAI.Geometry.NodalSets.Elliptic.RealCompactL2MapLemmas
import OAI.Geometry.NodalSets.Elliptic.RealFinitePositiveBounds
import OAI.Geometry.NodalSets.Elliptic.RealHessianDifferenceCutoffsLemmas
import OAI.Geometry.NodalSets.Elliptic.RealLocalizedDerivativeQuadratic
import OAI.Geometry.NodalSets.Elliptic.RealWeightedLocalDifferenceBound

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_interior_difference_bound (d : SphereEnergyData) (p : Base)
    (R0 r : ℝ) (hr : r < R0) (hR : R0 ≤ 1) :
    ∃ C > 0,
      ∀ (u : Yau.Jets.Coord → ℝ) (V0 P0 G : Fin 4 → Yau.Jets.Coord → ℝ)
        (DG : Fin 4 → Fin 4 → Yau.Jets.Coord → ℝ) (F0 : Yau.Jets.Coord → ℝ),
      let Q := Yau.realCenteredCube 4 R0
      MemLp u 2 (volume.restrict Q) →
      (∀ a, MemLp (V0 a) 2 (volume.restrict Q)) →
      (∀ a, MemLp (P0 a) 2 (volume.restrict Q)) →
      (∀ j, MemLp (G j) 2 (volume.restrict Q)) →
      (∀ j i, MemLp (DG j i) 2 (volume.restrict Q)) →
      MemLp F0 2 (volume.restrict Q) →
      (∀ a, P0 a =ᵐ[volume.restrict (interior Q)] V0 a) →
      (∀ j psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, u x*Yau.coordPartial psi x j)=-(∫ x in Q, V0 j x*psi x)) →
      (∀ j i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, G j x*Yau.coordPartial psi x i)=-(∫ x in Q, DG j i x*psi x)) →
      (∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*P0 a x*Yau.coordPartial psi x j)=
          (∫ x in Q, F0 x*psi x)-(∑ j, ∫ x in Q, G j x*Yau.coordPartial psi x j)) →
      ∀ E : ℝ, 0 ≤ E →
        (∫ x in Q, (u x)^2) ≤ E →
        (∀ a, (∫ x in Q, (V0 a x)^2) ≤ E) →
        (∫ x in Q, (F0 x)^2) ≤ E →
        (∀ j, (∫ x in Q, (G j x)^2) ≤ E) →
        (∀ j i, (∫ x in Q, (DG j i x)^2) ≤ E) →
        ∀ (i : Fin 4) (h : ℝ), |h| ≤ (R0-r)/8 →
          (∀ a, MemLp (Yau.realDifferenceQuotient i h (V0 a)) 2
            (volume.restrict (Yau.realCenteredCube 4 r))) ∧
          (∑ a, ∫ x in Yau.realCenteredCube 4 r, (Yau.realDifferenceQuotient i h (V0 a) x)^2) ≤ C*E := by
  obtain ⟨m,hm,K,hK,henergy⟩ := sphere_interior_localized_energy d p
  obtain ⟨eta,chi,he,hchi,hec,hchic,hes,hchis,heb,hchib,he1,hend⟩ :=
    Yau.real_nested_difference_cutoffs R0 r hr
  let Q := Yau.realCenteredCube 4 R0
  let Q0 := Yau.realCenteredCube 4 r
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 R0
  have hQ0 : IsCompact Q0 := Yau.realCenteredCube_isCompact 4 r
  have hcs : tsupport chi ⊆ Q := hchis.trans interior_subset
  have hetab (x : Yau.Jets.Coord) : |eta x| ≤ 1 := by rw [abs_of_nonneg (heb x).1]; exact (heb x).2
  have hends (i : Fin 4) (h : ℝ) (hh : |h| ≤ (R0-r)/8) (x : Yau.Jets.Coord) (hx : x ∈ tsupport eta) :
      x ∈ interior Q ∧ x+Pi.single i h ∈ interior Q ∧ chi x=1 ∧ chi (x+Pi.single i h)=1 := by
    have ht := hend i h hh x hx
    exact ⟨ht.1,ht.2.1,ht.2.2.1.eq_of_nhds,ht.2.2.2.eq_of_nhds⟩
  have hends0 (i : Fin 4) (h : ℝ) (hh : |h| ≤ (R0-r)/8) (x : Yau.Jets.Coord) (hx : x ∈ tsupport eta) :
      x ∈ Q ∧ x+Pi.single i h ∈ Q ∧ chi x=1 ∧ chi (x+Pi.single i h)=1 := by
    have ht := hends i h hh x hx
    exact ⟨interior_subset ht.1,interior_subset ht.2.1,ht.2.2⟩
  obtain ⟨CW,hCW,hWb⟩ := Yau.real_indicator_weighted_bound hQ eta he.continuous
  choose CG hCG hGb using fun i ↦ Yau.real_localized_derivative_quadratic hQ chi hchi hcs i
  obtain ⟨G0,hG0,hGmax⟩ := Yau.real_finite_positive_majorant CG
  choose CR hCR hRb using fun i a ↦ Yau.real_weighted_local_difference_bound hQ
    (fun x ↦ Yau.coordPartial eta x a) chi (Yau.real_coordPartial_smooth eta he a).continuous
    (hec.fderiv_apply ℝ (Pi.single a 1)) hchi hcs i
  obtain ⟨R1,hR1,hRmax⟩ := Yau.real_finite_positive_majorant (fun t : Fin 4 × Fin 4 ↦ CR t.1 t.2)
  let C := (4/m)*((16/m)*(1+8*G0)+K*(4*CW)+(K+m)*(8*R1))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro u V0 P0 G DG F0
  dsimp only
  intro hu hv hp hg hd hf hsame hweak hcomm hequation E hE hbu hbv hbf hbg hbd i h hh
  let V := fun a ↦ Q.indicator (V0 a)
  let q := Yau.realDifferenceQuotient i h (Q.indicator u)
  let T := fun a x ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
  let W := fun a x ↦ eta x*V a x
  let R := fun a x ↦ Yau.coordPartial eta x a*q x
  let F := Q.indicator F0
  have hwt := henergy R0 ((r+R0)/2) (by linarith) hR u V0 P0 G DG F0
    hu hv hp hg hd hf hsame hweak hcomm hequation eta chi he hec hetab hes hchi hcs i h
    (by linarith) (hends i h hh)
  have hWone (a : Fin 4) : (∫ x, (W a x)^2) ≤ CW*E :=
    (hWb (V0 a) (hv a)).2.trans (mul_le_mul_of_nonneg_left (hbv a) hCW.le)
  have hWsum : (∑ a, ∫ x, (W a x)^2) ≤ 4*CW*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hWone a)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using ht
  have hRone (a : Fin 4) : (∫ x, (R a x)^2) ≤ 2*R1*E := by
    have ht := (hRb i a u (V0 i) hu (hv i) (hweak i) h
      (fun x hx ↦ hends0 i h hh x (tsupport_fderiv_apply_subset ℝ (Pi.single a 1) hx))).2
    have hb := mul_le_mul_of_nonneg_left (add_le_add hbu (hbv i)) (hCR i a).le
    have hmax := mul_le_mul_of_nonneg_right (hRmax (i,a)) (show 0 ≤ E+E by positivity)
    exact ht.trans (hb.trans (hmax.trans_eq (by ring)))
  have hRsum : (∑ a, ∫ x, (R a x)^2) ≤ 8*R1*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hRone a)
    norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at ht
    exact ht.trans_eq (by ring)
  have hGone (j : Fin 4) : (∫ x, (chi x*DG j i x+Yau.coordPartial chi x i*G j x)^2) ≤ 2*G0*E := by
    have ht := (hGb i (G j) (DG j i) (hg j) (hd j i)).2
    have hb := mul_le_mul_of_nonneg_left (add_le_add (hbg j) (hbd j i)) (hCG i).le
    have hmax := mul_le_mul_of_nonneg_right (hGmax i) (show 0 ≤ E+E by positivity)
    exact ht.trans (hb.trans (hmax.trans_eq (by ring)))
  have hGsum : (∑ j, ∫ x, (chi x*DG j i x+Yau.coordPartial chi x i*G j x)^2) ≤ 8*G0*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hGone j)
    norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at ht
    exact ht.trans_eq (by ring)
  have hFint : (∫ x, (F x)^2) ≤ E := by
    have hind : (fun x ↦ (F x)^2)=Q.indicator (fun x ↦ (F0 x)^2) := by
      funext x
      by_cases hx : x ∈ Q
      · simp only [F,indicator_of_mem hx]
      · simp only [F,indicator_of_notMem hx,zero_pow (by decide : (2:ℕ)≠0)]
    change (∫ x, (fun y ↦ (F y)^2) x) ≤ _
    rw [hind,integral_indicator hQ.measurableSet]
    exact hbf
  have hglobal : (∑ a, ∫ x, (T a x)^2) ≤ C*E := by
    have ht := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add hFint hGsum) (show 0 ≤ 16/m by positivity))
      (mul_le_mul_of_nonneg_left hWsum hK.le))
      (mul_le_mul_of_nonneg_left hRsum (add_nonneg hK.le hm.le))
    have hb := hwt.2.trans (mul_le_mul_of_nonneg_left ht (show 0 ≤ 4/m by positivity))
    exact hb.trans_eq (by dsimp [C]; ring)
  have hident (a : Fin 4) (x : Yau.Jets.Coord) (hx : x ∈ Q0) :
      Yau.realDifferenceQuotient i h (V0 a) x=T a x := by
    have hxQ : x ∈ Q := Yau.realCenteredCube_mono hr.le hx
    have htQ : x+Pi.single i h ∈ Q := by
      apply Yau.realCenteredCube_shift i (h := -h) (r := r)
        (by simpa only [abs_neg] using (show |h| ≤ R0-r by linarith))
      simpa only [Pi.single_neg,add_neg_cancel_right] using hx
    dsimp [T,V]
    rw [(he1 x hx).eq_of_nhds,one_mul]
    simp only [Yau.realDifferenceQuotient,indicator_of_mem hxQ,indicator_of_mem htQ]
  refine ⟨fun a ↦ ?_,?_⟩
  · apply ((hwt.1 a).1.restrict Q0).ae_eq
    filter_upwards [ae_restrict_mem hQ0.measurableSet] with x hx
    exact (hident a x hx).symm
  · apply le_trans (Finset.sum_le_sum (fun a _ ↦ ?_)) hglobal
    have hEq : (∫ x in Q0, (Yau.realDifferenceQuotient i h (V0 a) x)^2)=
        ∫ x in Q0, (T a x)^2 := by
      apply setIntegral_congr_fun hQ0.measurableSet
      intro x hx
      change (Yau.realDifferenceQuotient i h (V0 a) x)^2=(T a x)^2
      rw [hident a x hx]
    rw [hEq]
    exact setIntegral_le_integral (hwt.1 a).1.integrable_sq
      (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))

end
end Yau.Target

end OAI
