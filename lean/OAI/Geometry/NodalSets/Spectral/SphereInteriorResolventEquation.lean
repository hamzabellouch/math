import OAI.Geometry.NodalSets.Charts.SphereChartDivergenceData
import OAI.Geometry.NodalSets.Elliptic.RealDifferenceQuotientTest

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_resolvent_interior_equation (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) {K : Set Yau.Jets.Coord} (hK : IsCompact K) (hsub : K ⊆ realFinCube 4)
    (psi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ K) :
    (∀ a j, IntegrableOn (fun x ↦ sphereChartPrincipalDensity d p x a j*
      (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x j) K) ∧
    IntegrableOn (fun x ↦ sphereChartResolventForcing d p f x*psi x) K ∧
    (∑ a, ∑ j, ∫ x in K, sphereChartPrincipalDensity d p x a j*
      (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x j) =
      ∫ x in K, sphereChartResolventForcing d p f x*psi x := by
  have hU (a : Fin 4) : MemLp (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) 2
      (volume.restrict K) := (Lp.memLp _).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hi (a j : Fin 4) : IntegrableOn (fun x ↦ sphereChartPrincipalDensity d p x a j*
      (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x j) K := by
    obtain ⟨_,_,hb⟩ := Yau.real_compact_multiplier_bound hK _
      (sphereChartPrincipalDensity_smooth d p a j).continuous
    exact ((hb _ (hU a)).1).integrable_mul
      (Yau.real_continuous_memLp_compact hK _ (Yau.real_coordPartial_smooth psi hp j).continuous)
  obtain ⟨_,_,hbF⟩ := sphereChartResolventForcing_bound d p hK
  have hiF := (hbF f).1.integrable_mul (Yau.real_continuous_memLp_compact hK psi hp.continuous)
  have he := (sphere_resolvent_divergence_weak d f p psi hp hc (hs.trans hsub)).2.2
  have hzD (x : Yau.Jets.Coord) (hx : x ∉ K) (j : Fin 4) : Yau.coordPartial psi x j=0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y ↦ Yau.coordPartial psi y j) (fun ht ↦ hx
      (hs (tsupport_fderiv_apply_subset ℝ (Pi.single j 1) ht)))
  have hrL : (∫ x in realFinCube 4, ∑ a, ∑ j, sphereChartPrincipalDensity d p x a j*
      (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x j) =
      ∫ x in K, ∑ a, ∑ j, sphereChartPrincipalDensity d p x a j*
        (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x j := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (realFinCube_isCompact 4).measurableSet hsub
    intro x hx
    simp only [hzD x hx.2,mul_zero,Finset.sum_const_zero]
  have hrR : (∫ x in realFinCube 4, sphereChartResolventForcing d p f x*psi x) =
      ∫ x in K, sphereChartResolventForcing d p f x*psi x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (realFinCube_isCompact 4).measurableSet hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx.2 (hs ht)),mul_zero]
  rw [hrL,hrR] at he
  rw [integral_finsetSum Finset.univ (fun a _ ↦ integrable_finsetSum Finset.univ (fun j _ ↦ hi a j))] at he
  simp_rw [integral_finsetSum Finset.univ (fun j _ ↦ hi _ j)] at he
  exact ⟨hi,hiF,he⟩

end
end Yau.Target

end OAI
