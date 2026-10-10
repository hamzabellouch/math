import Mathlib
import OAI.Analysis.CoulombRadii.Packets.ScreenBox
import OAI.Analysis.CoulombRadii.ThomasFermi.PatchGeometry
import OAI.Analysis.CoulombRadii.FieldAnalysis.ScaledOscillation

namespace OAI

noncomputable section

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical BigOperators Topology ContDiff
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ

omit [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfPotential_eq_density {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfPotential f=NeutralAtom.potentialOf (tfDensity Ω f) := by
  funext x
  apply integral_congr_ae
  filter_upwards [tfDensity_ae_tfExtend hΩ hf] with z hz
  change coulombKernel (x-z)*tfExtend Ω f z=coulombKernel (x-z)*tfDensity Ω f z
  rw [hz]

lemma tfPotential_ballCloud_integrable {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    {a : ℝ} (ha : 0 < a) (y : Space) :
    Integrable (fun z => tfPotential f z*ballCloud y a 1 z) := by
  rw [tfPotential_eq_density hΩ hf]
  exact potentialOf_ballCloud_integrable ((tfExtend_integrable hΩ f).congr
    (tfDensity_ae_tfExtend hΩ hf).symm) (tfDensity_measurable hΩ f) ha y

lemma tfPotential_ballCloud_le {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    {a : ℝ} (ha : 0 < a) (y : Space) :
    (∫ z, tfPotential f z*ballCloud y a 1 z)  ≤  tfPotential f y := by
  rw [tfPotential_eq_density hΩ hf]
  have hi := (tfExtend_integrable hΩ f).congr (tfDensity_ae_tfExtend hΩ hf).symm
  exact potentialOf_ballCloud_le hi (tfDensity_measurable hΩ f) (tfDensity_nonneg f) ha y
    (density_coulomb_integrable _ (tfDensity_nonneg f) (tfDensity_measurable hΩ f) hi
      (tfDensity_power_integrable hΩ hf) y)

lemma tfScreened_ballCloud_submean {Φ : Space → ℝ} {f : TFLp (volume.restrict Ω)}
    (hf : TFNonneg f) {a : ℝ} (ha : 0 < a) (y : Space)
    (hi : Integrable (fun z => Φ z*ballCloud y a 1 z))
    (he : (∫ z, Φ z*ballCloud y a 1 z)=Φ y) :
    Φ y-tfPotential f y  ≤  ∫ z, (Φ z-tfPotential f z)*ballCloud y a 1 z := by
  simp_rw [sub_mul]
  rw [integral_sub hi (tfPotential_ballCloud_integrable hΩ hf ha y),he]
  linarith [tfPotential_ballCloud_le hΩ hf ha y]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfEulerDensity_of_cap {c a v : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hv : v ≤ tfInteriorConstant c/a^4) :
    (max v 0/(c*(5/3:ℝ)))^(3/2:ℝ)  ≤
      (tfInteriorConstant c/(c*(5/3:ℝ)))^(3/2:ℝ)/a^6 := by
  have Hb : max v 0 ≤ tfInteriorConstant c/a^4 :=
    max_le hv (div_nonneg (tfInteriorConstant_nonneg c) (by positivity))
  have HH := Real.rpow_le_rpow (by positivity : 0 ≤ max v 0/(c*(5/3:ℝ)))
    (div_le_div_of_nonneg_right Hb (by positivity : 0 ≤ c*(5/3:ℝ))) (by norm_num : (0:ℝ) ≤ 3/2)
  apply HH.trans_eq
  rw [show tfInteriorConstant c/a^4/(c*(5/3:ℝ))=(tfInteriorConstant c/(c*(5/3:ℝ)))/a^4 by ring,
    Real.div_rpow (div_nonneg (tfInteriorConstant_nonneg c) (by positivity)) (by positivity),
    ←Real.rpow_natCast,←Real.rpow_mul ha.le]
  norm_num

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in

theorem tfScreened_interior_oscillation (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Set Space} (hΩ : MeasurableSet Ω)
      [IsFiniteMeasure (volume.restrict Ω)], ∀ {F : ℝ}, 0 ≤ F →
    ∀ (W : TFLq (volume.restrict Ω)), (∀ᵐ x ∂volume.restrict Ω, W x ≤ F) →
    ∀ (f : TFLp (volume.restrict Ω)), TFNonneg f →
    (∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) →
    ∀ (Φ : Space → ℝ), ContinuousOn Φ Ω → IsOpen Ω →
    W =ᵐ[volume.restrict Ω] Φ → NeutralAtom.HasWeakLaplacian Φ Ω (fun _ => 0) →
    ∀ (y : Space) (a : ℝ), 0 < a → Metric.closedBall y (4*a)⊆Ω →
    Integrable (fun z => Φ z*ballCloud y (2*a) 1 z) →
    (∫ z, Φ z*ballCloud y (2*a) 1 z)=Φ y →
    ∀ z∈Metric.closedBall y a,
      ‖(Φ z-tfPotential f z)-(Φ y-tfPotential f y)‖  ≤
        C*(‖z-y‖/a)*((a^4)⁻¹+max (-(Φ y-tfPotential f y)) 0) := by
  let A := (tfInteriorConstant c/(c*(5/3:ℝ)))^(3/2:ℝ)
  obtain ⟨C,hC,H⟩ := NeutralAtom.poisson_scaled_negative_oscillation
    (show 0 ≤ A from Real.rpow_nonneg (div_nonneg (tfInteriorConstant_nonneg c) (by positivity)) _) (tfInteriorConstant_nonneg c)
  refine ⟨C,hC,?_⟩
  intro Ω hΩ inst F hF W hW f hf hm Φ hΦ ho he hh y a ha hball hi hmean z hz
  let V := fun x => Φ x-tfPotential f x
  let σ := (Metric.closedBall y (3*a)).indicator (fun x => (max (V x) 0/(c*(5/3:ℝ)))^(3/2:ℝ))
  have h3 : Metric.closedBall y (3*a)⊆Ω :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  have h2 : Metric.ball y (2*a)⊆Ω :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))).trans hball
  have hP := tfPotential_continuous_of_minimizes hΩ hc hF W hW hf hm
  have hVc : ContinuousOn V Ω := hΦ.sub hP.continuousOn
  have hσc : ContinuousOn (fun x => (max (V x) 0/(c*(5/3:ℝ)))^(3/2:ℝ)) (Metric.closedBall y (3*a)) := by
    exact (((hVc.mono h3).sup continuousOn_const).div_const _).rpow_const (fun _ _ => Or.inr (by norm_num))
  have hσi : Integrable σ := (hσc.integrableOn_compact (isCompact_closedBall _ _)).integrable_indicator measurableSet_closedBall
  have hσ0 (x) : 0 ≤ σ x := indicator_nonneg (fun x _ => Real.rpow_nonneg (by positivity) _) x
  have hσb (x) (hx : x∈Metric.closedBall y (3*a)) : σ x ≤ A/a^6 := by
    rw [show σ x=(max (V x) 0/(c*(5/3:ℝ)))^(3/2:ℝ) from indicator_of_mem hx _]
    exact tfEulerDensity_of_cap hc ha (tfScreened_three_quarters hΩ hc hF W hW hf hm hΦ ho he hh ha hball hx)
  have hVL : NeutralAtom.HasWeakLaplacian V (Metric.ball y (2*a)) (fun x => 4*Real.pi*σ x) := by
    intro φ hφ hφc ht
    have h := (tfScreened_weak_equation hΩ hc hF W hW hf hm hΦ ho he hh).mono h2
    rw [h φ hφ hφc ht]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball y (2*a)
    · have hx3 : x∈Metric.closedBall y (3*a) :=
        (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) hx
      dsimp only [σ]
      rw [indicator_of_mem hx3,Real.div_rpow (le_max_right _ _) (by positivity)]
      dsimp only [V]
      ring
    · have hp0 : φ x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (ht h))
      simp only [hp0,mul_zero]
  apply H V σ y a ha (hVc.mono (Metric.ball_subset_closedBall.trans h3)) hVL hσi hσ0 hσb
    (fun x hx => tfScreened_three_quarters hΩ hc hF W hW hf hm hΦ ho he hh ha hball
      (Metric.closedBall_subset_closedBall (by linarith) hx))
    (tfScreened_ballCloud_submean hΩ hf (by positivity) y hi hmean) z hz

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
namespace Coulomb

def patchTFScreenedField {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : t ≤ 6*a) (y : Space)
    (hn : ∀ j, 20*a ≤ ‖S.position j-y‖) (z : Space) : ℝ :=
  coreScreenedField S u z-tfPotential (localTFMinimizer measurableSet_ball
    (coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn))) z

theorem exists_patch_TF_oscillation :
    ∃ C : ℝ, 0 < C ∧ ∀ {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (_ : 18*b ≤ a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space),
    SpatiallySupported u {z | t ≤ ‖z-y‖} →
    ∀ (hn : ∀ j, 20*a ≤ ‖S.position j-y‖) (z : Space), z∈Metric.closedBall y a →
      ‖patchTFScreenedField S u ha hb ht.2 y hn z-
        patchTFScreenedField S u ha hb ht.2 y hn y‖ ≤
      C*(‖z-y‖/a)*((a^4)⁻¹+max (-patchTFScreenedField S u ha hb ht.2 y hn y) 0) := by
  obtain ⟨C,hC,H⟩ := tfScreened_interior_oscillation thomasFermiKineticConstant thomasFermiKineticConstant_pos
  refine ⟨C,hC,?_⟩
  intro J k S u a b t ha hb hsmall ht y hu hn z hz
  let W := coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)
  have hW : ∀ᵐ x ∂volume.restrict (Metric.ball y (t-4*b)), W x ≤ totalCharge S/a := by
    filter_upwards [coreTFField_coe S u measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn),ae_restrict_mem measurableSet_ball] with x hx hy
    rw [hx]
    apply (sub_le_self _ (coreCoulombPotential_nonneg u x)).trans
    exact attraction_le_totalCharge_div S ha x (fun j => patch_nucleus_separation S ha hb ht.2 y hn j x hy)
  have hi : Integrable (fun z => coreScreenedField S u z*ballCloud y (2*a) 1 z) := by
    apply ((attraction_ballCloud_integrable S (by positivity : 0 < 2*a) y).sub
      (coreCoulombPotential_mul_integrable u _ (ballCloud_integrable (2*a) 1 y))).congr
    filter_upwards [] with z
    change attraction S z*ballCloud y (2*a) 1 z-coreCoulombPotential u z*ballCloud y (2*a) 1 z = _
    rw [coreScreenedField,sub_mul]
  have hm : (∫ z, coreScreenedField S u z*ballCloud y (2*a) 1 z)=coreScreenedField S u y := by
    simpa only [one_mul] using coreScreenedField_ballCloud S u hu (by positivity : 0 < 2*a) zero_le_one y
      (fun z hz => by change t ≤ ‖z-y‖ at hz; linarith [ht.1])
      (fun j => by linarith [hn j])
  exact H measurableSet_ball (div_nonneg (totalCharge_nonneg S) ha.le) W hW
    (localTFMinimizer measurableSet_ball W) (localTFMinimizer_nonneg measurableSet_ball W)
    (fun g hg => localTFMinimizer_minimizes measurableSet_ball W hg)
    (coreScreenedField S u) (patch_continuous_field S u ha hb ht.2 y hu hn) Metric.isOpen_ball
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (patch_harmonic_field S u ha hb ht.2 y hu hn) y a ha (patch_inner_ball ha hb hsmall ht.1 y) hi hm z hz

end Coulomb

end

end OAI
