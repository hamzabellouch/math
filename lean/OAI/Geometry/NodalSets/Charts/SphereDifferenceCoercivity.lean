import OAI.Geometry.NodalSets.Charts.SphereFluxDifferenceExpansion
import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientDifferenceBound
import OAI.Geometry.NodalSets.Elliptic.RealDifferenceCoercivity

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section
local instance sphereDifferenceCoercivityMeasurable : MeasurableSpace Base := borel Base
local instance sphereDifferenceCoercivityBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereChartPrincipalDensity_entries_bound (d : SphereEnergyData) (p : Base) :
    ∃ B > 0, ∀ x ∈ realFinCube 4, ∀ a j : Fin 4,
      |sphereChartPrincipalDensity d p x a j| ≤ B := by
  have hc : Continuous (sphereChartPrincipalDensity d p) := continuous_pi (fun a ↦
    continuous_pi (fun j ↦ (sphereChartPrincipalDensity_smooth d p a j).continuous))
  obtain ⟨B,hB,hb⟩ := ((realFinCube_isCompact 4).image hc).isBounded.exists_pos_norm_le
  refine ⟨B,hB,fun x hx a j ↦ ?_⟩
  exact (norm_le_pi_norm (sphereChartPrincipalDensity d p x a) j).trans
    ((norm_le_pi_norm (sphereChartPrincipalDensity d p x) a).trans (hb _ ⟨x,hx,rfl⟩))

theorem sphere_difference_square_test_derivative (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (ht : ContDiff ℝ ∞ theta) (i j : Fin 4) (h : ℝ)
    (h1 : ∀ x ∈ tsupport theta, eta =ᶠ[𝓝 x] (fun _ ↦ 1) ∧
      eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1)) (x : Yau.Jets.Coord) :
    theta x*theta x*Yau.realDifferenceQuotient i h
      (fun y ↦ eta y*(sphereChartDerivativeMap d p j z) y+
        Yau.coordPartial eta y j*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x+
      Yau.coordPartial (fun y ↦ theta y*theta y) x j*Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x =
    theta x*(theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x+
      2*(Yau.coordPartial theta x j*Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x)) := by
  rw [Yau.real_coordPartial_mul theta theta ht ht]
  by_cases hx : x ∈ tsupport theta
  · rw [Yau.real_cutoff_gradient_difference_of_one eta _ _ i j h x (h1 x hx).1 (h1 x hx).2]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hx]
    ring

theorem sphere_difference_pointwise_coercivity (d : SphereEnergyData) (p : Base) :
    ∃ m > 0, ∃ K > 0,
      ∀ (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
        (_ : ContDiff ℝ ∞ theta)
        (_ : tsupport theta ⊆ Yau.realCenteredCube 4 (3/4))
        (i : Fin 4) (h : ℝ) (_ : |h| ≤ 1/8)
        (_ : ∀ x ∈ tsupport theta, eta =ᶠ[𝓝 x] (fun _ ↦ 1) ∧
          eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1)),
      let q := Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y))
      let T := fun j x ↦ theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x
      let V := fun j x ↦ theta x*(sphereChartDerivativeMap d p j z) x
      let R := fun j x ↦ Yau.coordPartial theta x j*q x
      let P := fun j x ↦ theta x*(T j x+2*R j x)
      ∀ x, (m/2)*(∑ j, (T j x)^2) ≤
        (∑ j, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p z j) x*P j x)+
          K*((∑ j, (V j x)^2)+(∑ j, (R j x)^2)) := by
  obtain ⟨m,hm,C,hC,hell⟩ := sphereChartPrincipalDensity_elliptic d p (realFinCube_isCompact 4)
  obtain ⟨B,hB,hb⟩ := sphereChartPrincipalDensity_entries_bound d p
  obtain ⟨D,hD,hd⟩ := sphereChartPrincipalDensity_difference_bound d p
  let E := B+D
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨m,hm,256*E^2/m+4*E,by positivity,?_⟩
  intro z eta theta ht hts i h hh h1
  dsimp only
  intro x
  by_cases hx : x ∈ tsupport theta
  · have hx0 : x ∈ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num) (hts hx)
    have hxt : x+Pi.single i h ∈ realFinCube 4 := by
      apply Yau.realCenteredCube_shift i (h := -h) (r := 3/4)
        (by simpa only [abs_neg] using (show |h| ≤ (1:ℝ)-3/4 by linarith))
      simpa only [Pi.single_neg,add_neg_cancel_right] using hts hx
    let T : Fin 4 → ℝ := fun j ↦ theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x
    let V : Fin 4 → ℝ := fun j ↦ theta x*(sphereChartDerivativeMap d p j z) x
    let R : Fin 4 → ℝ := fun j ↦ Yau.coordPartial theta x j*
      Yau.realDifferenceQuotient i h (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x
    have hmB (a j : Fin 4) : |sphereChartPrincipalDensity d p (x+Pi.single i h) a j| ≤ E :=
      (hb _ hxt a j).trans (by dsimp [E]; linarith)
    have hnB (a j : Fin 4) :
        |Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x| ≤ E :=
      (hd a j i h x hx0 hxt).trans (by dsimp [E]; linarith)
    have hellT := (hell (x+Pi.single i h) hxt T).1
    have hc := Yau.real_difference_coercivity m E hm hE.le
    specialize hc (sphereChartPrincipalDensity d p (x+Pi.single i h))
      (fun a j ↦ Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x)
      T V R
    specialize hc hmB hnB hellT
    have heq (j : Fin 4) :
        Yau.realDifferenceQuotient i h (sphereChartFluxZero d p z j) x*
          (theta x*(T j+2*R j)) =
        (∑ a, (sphereChartPrincipalDensity d p (x+Pi.single i h) a j*T a+
          Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x*V a))*(T j+2*R j) := by
      rw [sphereChartFluxZero_difference_expansion d p z i j h x hx0 hxt]
      rw [← mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      dsimp [T,V]
      ring
    simp_rw [← heq] at hc
    exact hc
  · have hz := image_eq_zero_of_notMem_tsupport hx
    have hdz (j : Fin 4) : Yau.coordPartial theta x j=0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y ↦ Yau.coordPartial theta y j)
        (fun hs ↦ hx (tsupport_fderiv_apply_subset ℝ (Pi.single j 1) hs))
    simp only [hz,hdz,zero_mul,mul_zero,zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero,add_zero,le_refl]

end
end Yau.Target

end OAI
