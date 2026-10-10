import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.PatchNegativeCost
import OAI.Analysis.CoulombRadii.FieldAnalysis.BallCloudDuality

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma ballCloud_norm_bound {a : ℝ} (ha : 0<a) (y z : Space) :
    ‖ballCloud y a 1 z‖≤1/(4*Real.pi/3*a^3) := by
  change ‖uniformBall a 1 (z-y)‖≤_
  rw [Real.norm_of_nonneg (uniformBall_nonneg ha zero_le_one _)]
  exact uniformBall_le ha zero_le_one _

lemma density_ballCloud_test_integrable {ρ : Space → ℝ} (hi : Integrable ρ)
    (hm : Measurable ρ) {a : ℝ} (ha : 0<a) (y : Space) :
    Integrable (fun x => ρ x*(∫ z, coulombKernel (x-z)*ballCloud y a 1 z)) := by
  have H := (coulomb_pair_integrable hi hm (ballCloud_integrable a 1 y)
    (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y)).integral_prod_left
  apply H.congr
  filter_upwards [] with x
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

lemma potential_ballCloud_remainder {ρ : Space → ℝ} (hi : Integrable ρ)
    (hm : Measurable ρ) (hp : ∀ x, 0≤ρ x) {a : ℝ} (ha : 0<a) (y : Space)
    (hK : Integrable (fun x => coulombKernel (y-x)*ρ x)) :
    0≤NeutralAtom.potentialOf ρ y-coulombBilinear ρ (ballCloud y a 1) ∧
    NeutralAtom.potentialOf ρ y-coulombBilinear ρ (ballCloud y a 1)≤
      ∫ x in Metric.ball y a, ρ x*coulombKernel (y-x) := by
  have ht := density_ballCloud_test_integrable hi hm ha y
  let f := fun x => coulombKernel (y-x)*ρ x-
    ρ x*(∫ z, coulombKernel (x-z)*ballCloud y a 1 z)
  have he : NeutralAtom.potentialOf ρ y-coulombBilinear ρ (ballCloud y a 1)=∫ x, f x := by
    rw [coulombBilinear_iterated hi hm (ballCloud_integrable a 1 y)
      (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y)]
    exact (integral_sub hK ht).symm
  have hbound : ∀ᵐ x, 0≤f x ∧ f x≤(Metric.ball y a).indicator
      (fun x => ρ x*coulombKernel (y-x)) x := by
    filter_upwards [volume.ae_ne y] with x hxy
    have hlu := ballCloud_coulomb_le ha zero_le_one y x hxy
    have hl : 0≤∫ z, coulombKernel (x-z)*ballCloud y a 1 z :=
      integral_nonneg (fun z => mul_nonneg (coulombKernel_nonneg _) (uniformBall_nonneg ha zero_le_one _))
    have hpos : 0≤f x := by
      dsimp only [f]
      simp only [one_mul,coulombKernel_sub_comm x y] at hlu
      nlinarith [mul_le_mul_of_nonneg_left hlu (hp x)]
    refine ⟨hpos,?_⟩
    by_cases hx : x∈Metric.ball y a
    · rw [indicator_of_mem hx]
      dsimp only [f]
      nlinarith [mul_nonneg (hp x) hl]
    · rw [indicator_of_notMem hx]
      have hx' : a≤‖x-y‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hx
      dsimp only [f]
      rw [ballCloud_coulomb ha zero_le_one y x hx',one_mul,coulombKernel_sub_comm x y]
      nlinarith
  rw [he]
  refine ⟨integral_nonneg_of_ae (hbound.mono (fun _ h => h.1)),?_⟩
  rw [←integral_indicator measurableSet_ball]
  apply integral_mono_ae (hK.sub ht)
  · exact (hK.congr (Eventually.of_forall (fun x => mul_comm _ _))).indicator measurableSet_ball
  · exact hbound.mono (fun _ h => h.2)

lemma coulombBilinear_sub_ballCloud {ρ σ : Space → ℝ}
    (hρ : Integrable ρ) (hρm : Measurable ρ) (hσ : Integrable σ) (hσm : Measurable σ)
    {a : ℝ} (ha : 0<a) (y : Space) :
    coulombBilinear (fun z => ρ z-σ z) (ballCloud y a 1)=
      coulombBilinear ρ (ballCloud y a 1)-coulombBilinear σ (ballCloud y a 1) := by
  change coulombBilinear (ρ-σ) (ballCloud y a 1)=_
  rw [coulombBilinear_iterated (hρ.sub hσ) (hρm.sub hσm)
    (ballCloud_integrable a 1 y) (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y),
    coulombBilinear_iterated hρ hρm (ballCloud_integrable a 1 y)
      (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y),
    coulombBilinear_iterated hσ hσm (ballCloud_integrable a 1 y)
      (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y)]
  simp only [Pi.sub_apply, sub_mul]
  exact integral_sub (density_ballCloud_test_integrable hρ hρm ha y)
    (density_ballCloud_test_integrable hσ hσm ha y)

theorem potential_difference_coulomb_transfer {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {ρ σ : Space → ℝ}
    (hρ : MemLp ρ TFExponent (volume.restrict Ω))
    (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hρm : Measurable ρ) (hσm : Measurable σ)
    (hρp : ∀ z, 0≤ρ z) (hσp : ∀ z, 0≤σ z)
    (hρs : ∀ z∉Ω, ρ z=0) (hσs : ∀ z∉Ω, σ z=0)
    {a : ℝ} (ha : 0<a) (y : Space) (hball : Metric.ball y a⊆Ω) :
    |NeutralAtom.potentialOf ρ y-NeutralAtom.potentialOf σ y|≤
      Real.sqrt ((5/(2*a))*coulombBilinear (fun z => ρ z-σ z) (fun z => ρ z-σ z))+
      (∫ z in Metric.ball y a, ρ z*coulombKernel (y-z))+
      (∫ z in Metric.ball y a, σ z*coulombKernel (y-z)) := by
  have hρe := tfExtend_toLp hΩ hρ hρs
  have hσe := tfExtend_toLp hΩ hσ hσs
  have hρi : Integrable ρ := (tfExtend_integrable hΩ (hρ.toLp ρ)).congr hρe
  have hσi : Integrable σ := (tfExtend_integrable hΩ (hσ.toLp σ)).congr hσe
  have hρl : MemLp ρ TFExponent volume := (memLp_congr_ae hρe).mp (tfExtend_memLp hΩ _)
  have hσl : MemLp σ TFExponent volume := (memLp_congr_ae hσe).mp (tfExtend_memLp hΩ _)
  have hρpow := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hρl
    (Eventually.of_forall hρp)
  have hσpow := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hσl
    (Eventually.of_forall hσp)
  have Hρ := potential_ballCloud_remainder hρi hρm hρp ha y
    (density_coulomb_integrable _ hρp hρm hρi hρpow y)
  have Hσ := potential_ballCloud_remainder hσi hσm hσp ha y
    (density_coulomb_integrable _ hσp hσm hσi hσpow y)
  have hs : ∀ z∉Ω, ρ z-σ z=0 := fun z hz => by rw [hρs z hz,hσs z hz,sub_self]
  have H := raw_coulomb_ballCloud_duality hΩ (hρ.sub hσ) hs y ha hball
  have hq : 0≤(5/(2*a))*coulombBilinear (fun z => ρ z-σ z) (fun z => ρ z-σ z) :=
    mul_nonneg (by positivity) (raw_coulomb_nonneg hΩ (hρ.sub hσ) hs)
  have HT : |coulombBilinear (fun z => ρ z-σ z) (ballCloud y a 1)|≤Real.sqrt
      ((5/(2*a))*coulombBilinear (fun z => ρ z-σ z) (fun z => ρ z-σ z)) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt hq]
    exact H
  rw [coulombBilinear_sub_ballCloud hρi hρm hσi hσm ha y] at HT
  have HH := abs_le.mp HT
  apply abs_le.mpr
  constructor <;> linarith [Hρ.1,Hρ.2,Hσ.1,Hσ.2]

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma translated_coulomb_ball_integral (y : Space) {r : ℝ} (hr : 0≤r) :
    (∫ z in Metric.ball y r, coulombKernel (y-z))=2*Real.pi*r^2 := by
  have he : (Metric.ball y r).indicator (fun z => coulombKernel (y-z))=
      fun z => (Metric.ball (0:Space) r).indicator coulombKernel (y-z) := by
    funext z
    have hh : y-z∈Metric.ball (0:Space) r ↔ z∈Metric.ball y r := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero,norm_sub_rev]
    by_cases hz : z∈Metric.ball y r <;> simp [hh,hz]
  rw [←integral_indicator measurableSet_ball,he,integral_sub_left_eq_self,
    integral_indicator measurableSet_ball,coulombKernel_ball_integral hr]

lemma translated_coulomb_integrableOn_ball (y : Space) (r : ℝ) :
    IntegrableOn (fun z => coulombKernel (y-z)) (Metric.ball y r) := by
  rw [←integrable_indicator_iff measurableSet_ball]
  have he : (Metric.ball y r).indicator (fun z => coulombKernel (y-z))=
      fun z => (Metric.ball (0:Space) r).indicator coulombKernel (y-z) := by
    funext z
    have hh : y-z∈Metric.ball (0:Space) r ↔ z∈Metric.ball y r := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero,norm_sub_rev]
    by_cases hz : z∈Metric.ball y r <;> simp [hh,hz]
  rw [he]
  exact (integrable_comp_sub_left _ y).mpr
    ((coulombKernel_integrableOn_ball r).integrable_indicator measurableSet_ball)

lemma near_coulomb_of_density_cap {ρ : Space → ℝ} (y : Space) {r B : ℝ} (hr : 0≤r)
    (hi : IntegrableOn (fun z => ρ z*coulombKernel (y-z)) (Metric.ball y r))
    (hc : ∀ᵐ z ∂volume.restrict (Metric.ball y r), ρ z≤B) :
    (∫ z in Metric.ball y r, ρ z*coulombKernel (y-z))≤B*(2*Real.pi*r^2) := by
  calc
    _≤∫ z in Metric.ball y r, B*coulombKernel (y-z) := by
      apply integral_mono_ae hi ((translated_coulomb_integrableOn_ball y r).const_mul B)
      exact hc.mono (fun z hz => mul_le_mul_of_nonneg_right hz (coulombKernel_nonneg _))
    _=_ := by rw [integral_const_mul,translated_coulomb_ball_integral y hr]

theorem patch_tf_density_cap {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖})
    (hn : ∀ j, 20*a≤‖S.position j-y‖) :
    ∀ᵐ z ∂volume.restrict (Metric.closedBall y (3*a)),
      localTFDensity measurableSet_ball (coreTFField S u measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht.2 y hn)) z≤
        (tfInteriorConstant thomasFermiKineticConstant/
          (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6 := by
  let W := coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)
  have hW : ∀ᵐ z ∂volume.restrict (Metric.ball y (t-4*b)), W z≤totalCharge S/a := by
    filter_upwards [coreTFField_coe S u measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn),ae_restrict_mem measurableSet_ball] with z hz hmem
    rw [hz]
    exact (sub_le_self _ (coreCoulombPotential_nonneg u z)).trans
      (attraction_le_totalCharge_div S ha z
        (fun j => patch_nucleus_separation S ha hb ht.2 y hn j z hmem))
  exact tfDensity_interior_bound measurableSet_ball thomasFermiKineticConstant_pos
    (div_nonneg (totalCharge_nonneg S) ha.le) W hW
    (localTFMinimizer_nonneg measurableSet_ball W)
    (fun g hg => localTFMinimizer_minimizes measurableSet_ball W hg)
    (patch_continuous_field S u ha hb ht.2 y hu hn) Metric.isOpen_ball
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (patch_harmonic_field S u ha hb ht.2 y hu hn) ha (patch_inner_ball ha hb hsmall ht.1 y)

theorem patch_potential_transfer {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (hr : 0<r) (hra : r≤a)
    (spin : Spins m) (x : Configuration m)
    (hcs : SpatiallySupported (u.coreSlice spin x).normalized {z | t≤‖z-y‖}) :
    let W := coreTFField S (u.coreSlice spin x).normalized measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn)
    let σ := retainedFineDensity b (patchRetained y t b x) (position x)
    |NeutralAtom.potentialOf σ y-tfPotential (localTFMinimizer measurableSet_ball W) y|≤
      Real.sqrt ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn spin x)+
      (∫ z in Metric.ball y r, σ z*coulombKernel (y-z))+
      ((tfInteriorConstant thomasFermiKineticConstant/
          (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2) := by
  intro W σ
  let Ω := Metric.ball y (t-4*b)
  let ρ := localTFDensity measurableSet_ball W
  have hσ : MemLp σ TFExponent (volume.restrict Ω) := retainedFineDensity_memLp hb _ _
  have hρ : MemLp ρ TFExponent volume := tfDensity_memLp measurableSet_ball
    (localTFMinimizer_nonneg measurableSet_ball W)
  have hσs : ∀ z∉Ω, σ z=0 := retainedFineDensity_patch_support hb y t x
  have hρs : ∀ z∉Ω, ρ z=0 := fun z hz => tfDensity_eq_zero _ hz
  have hball : Metric.ball y r⊆Ω := by
    apply Metric.ball_subset_ball
    linarith [ht.1]
  have H := potential_difference_coulomb_transfer measurableSet_ball hσ (hρ.restrict (s := Ω))
    (retainedFineDensity_measurable b _ _) (tfDensity_measurable measurableSet_ball _)
    (retainedFineDensity_nonneg b _ _) (tfDensity_nonneg _) hσs hρs hr y hball
  have HG := rawTF_gap_coulomb measurableSet_ball
    (coreScreenedField S (u.coreSlice spin x).normalized) W
    (coreTFField_coe S _ measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)) hσ
    (Eventually.of_forall (retainedFineDensity_nonneg b _ _)) hσs
  have Hsq : Real.sqrt ((5/(2*r))*coulombBilinear (fun z => σ z-ρ z) (fun z => σ z-ρ z))≤
      Real.sqrt ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn spin x) := by
    apply Real.sqrt_le_sqrt
    have HH := mul_le_mul_of_nonneg_left HG (show 0≤5/(2*r) by positivity)
    convert HH using 1; (try dsimp only [patchSliceTFGap,σ,ρ,W]); first | rfl | ring
  have hiρ : Integrable ρ := (tfExtend_integrable measurableSet_ball
    (localTFMinimizer measurableSet_ball W)).congr
      (tfDensity_ae_tfExtend measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W)).symm
  have hnear := near_coulomb_of_density_cap y hr.le
    (((density_coulomb_integrable ρ (tfDensity_nonneg _) (tfDensity_measurable measurableSet_ball _)
      hiρ (tfDensity_power_integrable measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W)) y).congr
        (Eventually.of_forall (fun z => mul_comm _ _))).integrableOn (s := Metric.ball y r))
    (ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith : r≤3*a)))
      (patch_tf_density_cap S (u.coreSlice spin x).normalized ha hb hsmall ht y hcs hn))
  rw [tfPotential_eq_density measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W)]
  exact H.trans (add_le_add (add_le_add Hsq le_rfl) hnear)

end Coulomb

end

end OAI
