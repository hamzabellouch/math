import OAI.Geometry.NodalSets.Elliptic.RealCompactMultiplierLemmas
import OAI.Geometry.NodalSets.Spectral.SphereResolventVariational

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section
local instance sphereChartDivergenceDataMeasurable : MeasurableSpace Base := borel Base
local instance sphereChartDivergenceDataBorel : BorelSpace Base := ⟨rfl⟩

def sphereChartPrincipalDensity (d : SphereEnergyData) (p : Base) (x : Yau.Jets.Coord)
    (i j : Fin 4) : ℝ := roundCoordDensity x*intrinsicRealPrincipal d.tensor p x i j

def sphereChartResolventForcing (d : SphereEnergyData) (p : Base) (f : SphereWeightedL2 d)
    (x : Yau.Jets.Coord) : ℝ :=
  roundCoordDensity x*d.density (sphereChartCoordMap p x)*
    (f (sphereChartCoordMap p x)-(sphereL2Resolvent d f) (sphereChartCoordMap p x))

theorem sphereChartPrincipalDensity_smooth (d : SphereEnergyData) (p : Base) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ sphereChartPrincipalDensity d p x i j) :=
  roundCoordDensity_smooth.mul (intrinsicRealPrincipal_smooth d.tensor d.smooth d.symm d.pos p i j)

theorem sphereChartPrincipalDensity_symmetric (d : SphereEnergyData) (p : Base)
    (x : Yau.Jets.Coord) (i j : Fin 4) :
    sphereChartPrincipalDensity d p x i j=sphereChartPrincipalDensity d p x j i := by
  unfold sphereChartPrincipalDensity
  rw [intrinsicRealPrincipal_symmetric d.tensor d.symm]

theorem sphereChartPrincipalDensity_elliptic (d : SphereEnergyData) (p : Base)
    {K : Set Yau.Jets.Coord} (hK : IsCompact K) :
    ∃ c > 0, ∃ C > 0, ∀ x ∈ K, ∀ xi : Fin 4 → ℝ,
      c*(∑ i, xi i^2) ≤ (∑ i, ∑ j, xi i*sphereChartPrincipalDensity d p x i j*xi j) ∧
      (∑ i, ∑ j, xi i*sphereChartPrincipalDensity d p x i j*xi j) ≤ C*(∑ i, xi i^2) := by
  apply compact_matrix_uniform_ellipticity (sphereChartPrincipalDensity d p)
    (fun i j ↦ (sphereChartPrincipalDensity_smooth d p i j).continuous) _ hK
  intro x
  exact (intrinsicRealPrincipal_posDef d.tensor d.symm d.pos p x).smul (roundCoordDensity_pos x)

theorem sphereChartResolventForcing_bound (d : SphereEnergyData) (p : Base)
    {K : Set Yau.Jets.Coord} (hK : IsCompact K) :
    ∃ C > 0, ∀ f : SphereWeightedL2 d,
      MemLp (sphereChartResolventForcing d p f) 2 (volume.restrict K) ∧
      (∫ x in K, (sphereChartResolventForcing d p f x)^2) ≤
        C*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  let a := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)
  have ha : Continuous a := roundCoordDensity_smooth.continuous.mul
    (d.continuous.comp (sphereChartCoordMap_smooth p).continuous)
  obtain ⟨B,hB,hb⟩ := Yau.real_compact_multiplier_bound hK a ha
  obtain ⟨D,hD,hd⟩ := sphereWeightedL2_compact_chart_bound d p hK
  refine ⟨2*(B*D),by positivity,?_⟩
  intro f
  let g := f-sphereL2Resolvent d f
  obtain ⟨hg,hgb⟩ := hd g
  obtain ⟨hm,hmb⟩ := hb _ hg
  have he : (fun x ↦ a x*g (sphereChartCoordMap p x)) =ᵐ[volume.restrict K]
      sphereChartResolventForcing d p f := by
    have h := (sphereWeightedMeasure_ae_chart_iff d p (fun x ↦ g x=f x-(sphereL2Resolvent d f) x)).mp
      (Lp.coeFn_sub f (sphereL2Resolvent d f))
    filter_upwards [ae_restrict_of_ae h] with x hx
    simp only [sphereChartResolventForcing,← hx,a]
  refine ⟨hm.ae_eq he,?_⟩
  have hi : (∫ x in K, (sphereChartResolventForcing d p f x)^2) = ∫ x in K, (a x*g (sphereChartCoordMap p x))^2 :=
    integral_congr_ae (he.fun_comp (fun t : ℝ ↦ t^2)).symm
  rw [hi]
  have hn : ‖g‖ ≤ ‖f‖+‖sphereWeakSolution d f‖ :=
    (norm_sub_le f (sphereL2Resolvent d f)).trans (add_le_add_right
      (sphereEnergyL2Map_apply_norm_le d (sphereWeakSolution d f)) _)
  have hns : ‖g‖^2 ≤ 2*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
    nlinarith [norm_nonneg g,norm_nonneg f,norm_nonneg (sphereWeakSolution d f),
      sq_nonneg (‖f‖-‖sphereWeakSolution d f‖)]
  calc
    _ ≤ B*(D*‖g‖^2) := hmb.trans (mul_le_mul_of_nonneg_left hgb hB.le)
    _ ≤ B*(D*(2*(‖f‖^2+‖sphereWeakSolution d f‖^2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hns hD.le) hB.le
    _ = _ := by ring

theorem sphere_resolvent_divergence_weak (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ realFinCube 4) :
    IntegrableOn (fun x ↦ ∑ i, ∑ j, sphereChartPrincipalDensity d p x i j*
      (sphereChartDerivativeMap d p i (sphereWeakSolution d f)) x*Yau.coordPartial phi x j) (realFinCube 4) ∧
    IntegrableOn (fun x ↦ sphereChartResolventForcing d p f x*phi x) (realFinCube 4) ∧
    (∫ x in realFinCube 4, ∑ i, ∑ j, sphereChartPrincipalDensity d p x i j*
      (sphereChartDerivativeMap d p i (sphereWeakSolution d f)) x*Yau.coordPartial phi x j) =
      ∫ x in realFinCube 4, sphereChartResolventForcing d p f x*phi x := by
  obtain ⟨hF,hM,hR,he⟩ := sphere_resolvent_chart_variational d f p phi hp hc hs
  have heF : (fun x ↦ roundCoordDensity x*∑ i, (sphereChartDerivativeMap d p i (sphereWeakSolution d f)) x*
      (∑ j, intrinsicRealPrincipal d.tensor p x i j*Yau.coordPartial phi x j)) =
      fun x ↦ ∑ i, ∑ j, sphereChartPrincipalDensity d p x i j*
        (sphereChartDerivativeMap d p i (sphereWeakSolution d f)) x*Yau.coordPartial phi x j := by
    funext x
    simp only [sphereChartPrincipalDensity,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heF] at hF he
  have heR : (fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)*
      f (sphereChartCoordMap p x)*phi x - roundCoordDensity x*d.density (sphereChartCoordMap p x)*
      (sphereEnergyL2Map d (sphereWeakSolution d f)) (sphereChartCoordMap p x)*phi x) =
      fun x ↦ sphereChartResolventForcing d p f x*phi x := by
    funext x
    unfold sphereChartResolventForcing
    change _ = _*(_-(sphereEnergyL2Map d (sphereWeakSolution d f)) (sphereChartCoordMap p x))*phi x
    ring
  refine ⟨hF,by rw [← heR]; exact hR.sub hM,?_⟩
  rw [← heR,integral_sub hR hM]
  linarith only [he]

end
end Yau.Target

end OAI
