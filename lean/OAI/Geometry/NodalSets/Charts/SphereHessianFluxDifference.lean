import OAI.Geometry.NodalSets.Charts.SphereWeakHessianSymmetry
import OAI.Geometry.NodalSets.Elliptic.RealBallCubeContainmentLemmas

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
noncomputable section

theorem sphere_hessian_flux_difference_ae (d : SphereEnergyData) (p : Base)
    (H : Fin 4 → Fin 4 → Yau.Jets.Coord → ℝ)
    (hsym : ∀ a k, (H a k) =ᵐ[volume.restrict
      (interior (Yau.realCenteredCube 4 (1/2)))] H k a)
    (k i : Fin 4) (h : ℝ) (hh : |h| ≤ 1/32) :
    let Q := Yau.realCenteredCube 4 (1/2)
    let V := fun a ↦ Q.indicator (H k a)
    let A := fun j ↦ Q.indicator (fun x ↦ ∑ a, sphereChartPrincipalDensity d p x a j*H a k x)
    ∀ᵐ x ∂volume, x ∈ Yau.realCenteredCube 4 (3/8) → ∀ j,
      Yau.realDifferenceQuotient i h (A j) x =
        ∑ a, (sphereChartPrincipalDensity d p (x+Pi.single i h) a j*
            Yau.realDifferenceQuotient i h (V a) x+
          Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x*V a x) := by
  dsimp only
  let Q := Yau.realCenteredCube 4 (1/2)
  have hsymall : ∀ᵐ x ∂volume.restrict (interior Q), ∀ a, H a k x=H k a x :=
    ae_all_iff.mpr (fun a ↦ hsym a k)
  have ht := Yau.real_ae_translation_endpoints isOpen_interior.measurableSet
    (fun x ↦ ∀ a, H a k x=H k a x) hsymall (Pi.single i h)
  filter_upwards [ht] with x hx
  intro hxsmall j
  have hxint : x ∈ interior Q := Yau.realCenteredCube_subset_interior (by norm_num) hxsmall
  have hxshift : x+Pi.single i h ∈ Yau.realCenteredCube 4 (7/16) := by
    apply Yau.realCenteredCube_shift i (h := -h) (r := 3/8)
      (by simpa only [abs_neg] using (show |h| ≤ (7/16:ℝ)-3/8 by linarith))
    simpa only [Pi.single_neg,add_neg_cancel_right] using hxsmall
  have htint : x+Pi.single i h ∈ interior Q :=
    Yau.realCenteredCube_subset_interior (by norm_num) hxshift
  have hxe := hx.1 hxint
  have hte := hx.2 htint
  have hxQ : x ∈ Q := interior_subset hxint
  have htQ : x+Pi.single i h ∈ Q := interior_subset htint
  have hid : Yau.realDifferenceQuotient i h
      (Q.indicator (fun y ↦ ∑ a, sphereChartPrincipalDensity d p y a j*H a k y)) x =
      Yau.realDifferenceQuotient i h
        (fun y ↦ ∑ a, sphereChartPrincipalDensity d p y a j*(Q.indicator (H k a)) y) x := by
    simp only [Yau.realDifferenceQuotient,indicator_of_mem hxQ,indicator_of_mem htQ,hxe,hte]
  rw [hid,Yau.realDifferenceQuotient_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact Yau.realDifferenceQuotient_mul i h _ _ x

end
end Yau.Target

end OAI
