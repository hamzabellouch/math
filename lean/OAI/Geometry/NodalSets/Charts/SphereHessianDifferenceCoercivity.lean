import OAI.Geometry.NodalSets.Charts.SphereDifferenceCoercivity
import OAI.Geometry.NodalSets.Charts.SphereHessianFluxDifference
import OAI.Geometry.NodalSets.Elliptic.RealSquareCutoffWeakGradient

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_hessian_difference_coercivity (d : SphereEnergyData) (p : Base) :
    ∃ m > 0, ∃ K > 0,
      ∀ (H : Fin 4 → Fin 4 → Yau.Jets.Coord → ℝ),
        (∀ a k, (H a k) =ᵐ[volume.restrict
          (interior (Yau.realCenteredCube 4 (1/2)))] H k a) →
        ∀ (k i : Fin 4) (h : ℝ), |h| ≤ 1/32 →
        ∀ (eta q : Yau.Jets.Coord → ℝ),
          tsupport eta ⊆ Yau.realCenteredCube 4 (3/8) →
        let Q := Yau.realCenteredCube 4 (1/2)
        let V := fun a ↦ Q.indicator (H k a)
        let A := fun j ↦ Q.indicator (fun x ↦ ∑ a, sphereChartPrincipalDensity d p x a j*H a k x)
        let T := fun a x ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
        let W := fun a x ↦ eta x*V a x
        let R := fun a x ↦ Yau.coordPartial eta x a*q x
        let P := Yau.realSquareCutoffGradient eta q (fun a ↦ Yau.realDifferenceQuotient i h (V a))
        ∀ᵐ x ∂volume, (m/2)*(∑ a, (T a x)^2) ≤
          (∑ j, Yau.realDifferenceQuotient i h (A j) x*P j x)+
            K*((∑ a, (W a x)^2)+(∑ a, (R a x)^2)) := by
  obtain ⟨m,hm,C,hC,hell⟩ := sphereChartPrincipalDensity_elliptic d p (realFinCube_isCompact 4)
  obtain ⟨B,hB,hb⟩ := sphereChartPrincipalDensity_entries_bound d p
  obtain ⟨D,hD,hd⟩ := sphereChartPrincipalDensity_difference_bound d p
  let E := B+D
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨m,hm,256*E^2/m+4*E,by positivity,?_⟩
  intro H hsym k i h hh eta q hs
  dsimp only
  have hflux := sphere_hessian_flux_difference_ae d p H hsym k i h hh
  filter_upwards [hflux] with x hflux
  let Q := Yau.realCenteredCube 4 (1/2)
  let V := fun a ↦ Q.indicator (H k a)
  let A := fun j ↦ Q.indicator (fun y ↦ ∑ a, sphereChartPrincipalDensity d p y a j*H a k y)
  let T : Fin 4 → ℝ := fun a ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
  let W : Fin 4 → ℝ := fun a ↦ eta x*V a x
  let R : Fin 4 → ℝ := fun a ↦ Yau.coordPartial eta x a*q x
  by_cases hx : x ∈ tsupport eta
  · have hxsmall := hs hx
    have hx0 : x ∈ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num) hxsmall
    have hxt : x+Pi.single i h ∈ realFinCube 4 := by
      apply Yau.realCenteredCube_shift i (h := -h) (r := 3/8)
        (by simpa only [abs_neg] using (show |h| ≤ (1:ℝ)-3/8 by linarith))
      simpa only [Pi.single_neg,add_neg_cancel_right] using hxsmall
    have hmB (a j : Fin 4) : |sphereChartPrincipalDensity d p (x+Pi.single i h) a j| ≤ E :=
      (hb _ hxt a j).trans (by dsimp [E]; linarith)
    have hnB (a j : Fin 4) :
        |Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x| ≤ E :=
      (hd a j i h x hx0 hxt).trans (by dsimp [E]; linarith)
    have hellT := (hell (x+Pi.single i h) hxt T).1
    have hc := Yau.real_difference_coercivity m E hm hE.le
    specialize hc (sphereChartPrincipalDensity d p (x+Pi.single i h))
      (fun a j ↦ Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x)
      T W R
    specialize hc hmB hnB hellT
    have heq (j : Fin 4) : Yau.realDifferenceQuotient i h (A j) x*
        Yau.realSquareCutoffGradient eta q (fun a ↦ Yau.realDifferenceQuotient i h (V a)) j x =
        (∑ a, (sphereChartPrincipalDensity d p (x+Pi.single i h) a j*T a+
          Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x*W a))*(T j+2*R j) := by
      have hgrad : Yau.realSquareCutoffGradient eta q
          (fun a ↦ Yau.realDifferenceQuotient i h (V a)) j x=eta x*(T j+2*R j) := by
        dsimp [Yau.realSquareCutoffGradient,T,R]
        ring
      rw [hgrad,hflux hxsmall j,← mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      dsimp [T,W]
      ring
    simp_rw [← heq] at hc
    exact hc
  · have hz := image_eq_zero_of_notMem_tsupport hx
    have hdz (j : Fin 4) : Yau.coordPartial eta x j=0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y ↦ Yau.coordPartial eta y j)
        (fun hj ↦ hx (tsupport_fderiv_apply_subset ℝ (Pi.single j 1) hj))
    simp only [Yau.realSquareCutoffGradient,hz,hdz,zero_mul,mul_zero,
      zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero,add_zero,le_refl]

end
end Yau.Target

end OAI
