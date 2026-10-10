import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.InnerFieldCap
import OAI.Analysis.CoulombIonization.RadialBounds.CoulombTailStatistic

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter Set
open scoped BigOperators

def innerFieldVolume (h : ℝ) : ℝ := volume.real (innerFieldTestAnnulus h)
lemma innerFieldVolume_nonneg (h : ℝ) : 0 ≤ innerFieldVolume h := measureReal_nonneg

lemma positiveCoreField_annular_sq_integrable {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {Z lam h : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    IntegrableOn (fun z => (max (normalizedCoreField Z lam psi z) 0)^2) (innerFieldTestAnnulus h) := by
  let : IsFiniteMeasure (volume.restrict (innerFieldTestAnnulus h)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact innerFieldTestAnnulus_finite h⟩
  apply (integrable_const ((Z/h)^2)).mono'
    (((normalizedCoreField_measurable hpsi Z lam).max measurable_const).pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (innerFieldTestAnnulus_measurable h)] with z hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (le_max_right _ _) (normalizedCoreField_pos_le psi hZ hlam hh hz.1) 2

lemma positiveCoreField_annular_cauchy {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {Z lam h : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    (∫ z in innerFieldTestAnnulus h, max (normalizedCoreField Z lam psi z) 0)^2 ≤
      innerFieldVolume h*(∫ z in innerFieldTestAnnulus h, (max (normalizedCoreField Z lam psi z) 0)^2) := by
  let mu := volume.restrict (innerFieldTestAnnulus h)
  let : IsFiniteMeasure mu := ⟨by rw [Measure.restrict_apply_univ]; exact innerFieldTestAnnulus_finite h⟩
  let f := fun z => max (normalizedCoreField Z lam psi z) 0
  have h1 : Integrable f mu := positiveCoreField_annular_integrable hpsi hZ hlam hh
  have h2 : Integrable (fun z => f z^2) mu := positiveCoreField_annular_sq_integrable hpsi hZ hlam hh
  have hc := weighted_sum_integral_cauchy (fun _ : Unit => mu)
    (fun _ _ => (1:ℝ)) (fun _ z => f z) (fun _ _ => (1:ℝ))
    (fun _ _ => zero_le_one)
    (fun _ => by simpa only [mul_one] using h2)
    (fun _ => by simpa only [one_pow,one_mul] using (integrable_const (1:ℝ) : Integrable (fun _ : Space => (1:ℝ)) mu))
    (fun _ => by simpa only [mul_one] using h1)
  simp only [Finset.univ_unique,Finset.sum_singleton,mul_one,one_pow,integral_const,
    smul_eq_mul,Measure.real] at hc
  have hsq := pow_le_pow_left₀ (integral_nonneg (fun z => le_max_right _ _)) hc 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg (fun z => sq_nonneg _)),
    Real.sq_sqrt (by dsimp [mu]; positivity)] at hsq
  simpa only [f,mu,innerFieldVolume,Measure.real,Measure.restrict_apply_univ,mul_comm] using hsq

def innerCapStatistic {N : ℕ} (psi : FormVector N) (Z lam h : ℝ) : ℝ :=
  3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h*
    (∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z psi)+
    3*lam^2*formMass psi+3*(16*packetPotentialConstant)^2*rawWeightedMoment psi (coulombTailWeight h)

lemma innerCapStatistic_nonneg {N : ℕ} (psi : FormVector N) (Z lam h : ℝ) :
    0 ≤ innerCapStatistic psi Z lam h := by
  unfold innerCapStatistic
  have hv := innerFieldVolume_nonneg h
  have hf : 0 ≤ ∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z psi :=
    integral_nonneg (fun z => coreFieldSquare_nonneg Z lam z psi)
  have hm := formMass_nonneg psi
  have ht := rawWeightedMoment_nonneg psi (coulombTailWeight h)
  positivity

theorem actualInnerBoundaryCap_sq_le_statistic {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {Z lam h : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    (actualInnerBoundaryCap psi Z lam h)^2*formMass psi ≤ innerCapStatistic psi Z lam h := by
  let A := packetDensityConstant/(h/4)^3
  let B := 16*packetPotentialConstant
  let U := ∫ z in innerFieldTestAnnulus h, max (normalizedCoreField Z lam psi z) 0
  let T := ∫ a, ‖a‖⁻¹ ∂(actualParticleSource psi).restrict {a | h < ‖a‖}
  let M := formMass psi
  have hM : 0 ≤ M := formMass_nonneg psi
  have hU := mul_le_mul_of_nonneg_right (positiveCoreField_annular_cauchy hpsi hZ hlam hh) hM
  have hT := actual_tail_square_le hpsi hh
  have hx : (A*U+lam+B*T)^2 ≤ 3*((A*U)^2+lam^2+(B*T)^2) := by
    nlinarith only [sq_nonneg (A*U-lam),sq_nonneg (A*U-B*T),sq_nonneg (lam-B*T)]
  have hxm := mul_le_mul_of_nonneg_right hx hM
  have he : (∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z psi) =
      (∫ z in innerFieldTestAnnulus h, (max (normalizedCoreField Z lam psi z) 0)^2)*M := by
    exact integral_mul_const M _
  unfold actualInnerBoundaryCap innerCapStatistic
  rw [he]
  change (A*U+lam+B*T)^2*M ≤
    3*A^2*innerFieldVolume h*((∫ z in innerFieldTestAnnulus h, (max (normalizedCoreField Z lam psi z) 0)^2)*M)+
      3*lam^2*M+3*B^2*rawWeightedMoment psi (coulombTailWeight h)
  have h1 := mul_le_mul_of_nonneg_left hU (show 0 ≤ 3*A^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hT (show 0 ≤ 3*B^2 by positivity)
  nlinarith only [hxm,h1,h2]

theorem actual_inner_exterior_sq_statistic {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) (hm : formMass psi ≠ 0) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) {y : Space} (hy : 2*h ≤ ‖y‖) :
    (max (sourceField Z (actualInnerSource psi h) y) 0)^2*formMass psi ≤
      innerCapStatistic psi Z lam h*((2*h)/‖y‖)^2 := by
  have hcap := actual_inner_exterior_cap hpsi hm hZ hlam hh hy
  have hc := actualInnerBoundaryCap_nonneg psi Z hlam hh
  have hq : 0 ≤ (2*h)/‖y‖ := by positivity
  have hf : max (sourceField Z (actualInnerSource psi h) y) 0 ≤
      actualInnerBoundaryCap psi Z lam h*((2*h)/‖y‖) := by
    apply max_le
    · simpa only [mul_div_assoc] using hcap
    · exact mul_nonneg hc hq
  have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_right _ _) hf 2) (formMass_nonneg psi)
  calc
    _ ≤ (actualInnerBoundaryCap psi Z lam h*((2*h)/‖y‖))^2*formMass psi := hp
    _ = (actualInnerBoundaryCap psi Z lam h)^2*formMass psi*((2*h)/‖y‖)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (actualInnerBoundaryCap_sq_le_statistic hpsi hZ hlam hh) (sq_nonneg _)

end
open MeasureTheory Filter Set Metric
open scoped BigOperators

def innerFieldAnnulusWeight (h : ℝ) : Space → ℝ :=
  (innerFieldTestAnnulus h).indicator (fun _ => 1)
lemma innerFieldAnnulusWeight_integrable (h : ℝ) : Integrable (innerFieldAnnulusWeight h) := by
  rw [innerFieldAnnulusWeight,integrable_indicator_iff (innerFieldTestAnnulus_measurable h)]
  exact integrableOn_const (C := (1:ℝ)) (hs := innerFieldTestAnnulus_finite h |>.ne)
lemma innerFieldAnnulusWeight_nonneg (h : ℝ) (z : Space) : 0 ≤ innerFieldAnnulusWeight h z :=
  indicator_nonneg (fun _ _ => zero_le_one) z
lemma innerFieldAnnulusWeight_separation (h : ℝ) (z : Space)
    (hz : innerFieldAnnulusWeight h z ≠ 0) : h ≤ ‖z‖ := by
  by_contra! hc
  exact hz (indicator_of_notMem (by intro hd; exact (not_le_of_gt hc) hd.1) _)
lemma innerFieldAnnulus_weight_eq (h : ℝ) (f : Space → ℝ) :
    (∫ z, f z*innerFieldAnnulusWeight h z) = ∫ z in innerFieldTestAnnulus h, f z := by
  rw [←integral_indicator (innerFieldTestAnnulus_measurable h)]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by by_cases hz : z ∈ innerFieldTestAnnulus h <;> simp [innerFieldAnnulusWeight,hz])

lemma coreFieldSquare_annular_statistic_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    Integrable (fun u => ∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z (coreSlice ψ t u)) := by
  have hi := (coreFieldSquare_weighted_prod_integrable hψ t hZ hlam hh
    (innerFieldAnnulusWeight_integrable h) (innerFieldAnnulusWeight_nonneg h)
    (innerFieldAnnulusWeight_separation h)).integral_prod_left
  simpa only [innerFieldAnnulus_weight_eq] using hi

lemma coreFieldSquare_annular_fubini {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    coreLawAverage ψ (fun φ => ∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z φ) =
      ∫ z in innerFieldTestAnnulus h, coreLawAverage ψ (coreFieldSquare Z lam z) := by
  have he := coreFieldSquare_weighted_fubini hψ Z lam hZ hlam hh
    (innerFieldAnnulusWeight_integrable h) (innerFieldAnnulusWeight_nonneg h)
    (innerFieldAnnulusWeight_separation h)
  simpa only [innerFieldAnnulus_weight_eq] using he

lemma innerCapStatistic_coreSlice_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    Integrable (fun u => innerCapStatistic (coreSlice ψ t u) Z lam h) := by
  unfold innerCapStatistic
  exact (((coreFieldSquare_annular_statistic_integrable hψ t hZ hlam hh).const_mul _).add
    ((hψ.coreSlice_mass_integrable t).const_mul _)).add
    ((rawWeightedMoment_coreSlice_integrable hψ (coulombTailWeight_measurable h)
      (coulombTailWeight_nonneg h) (coulombTailWeight_le hh) t).const_mul _)

namespace CoreObservationGraph

def innerCapAverage (G : CoreObservationGraph) (Z lam h : ℝ) : ℝ :=
  coreLawAverage G.vector (fun φ => innerCapStatistic φ Z lam h)

lemma fieldMoment_annular_integrable (G : CoreObservationGraph) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    IntegrableOn (G.fieldMoment Z lam) (innerFieldTestAnnulus h) := by
  have hi := G.fieldMoment_weighted_integrable hZ hlam hh (innerFieldAnnulusWeight_integrable h)
    (innerFieldAnnulusWeight_nonneg h) (innerFieldAnnulusWeight_separation h)
  rw [←integrable_indicator_iff (innerFieldTestAnnulus_measurable h)]
  apply hi.congr
  exact ae_of_all _ (fun z => by by_cases hz : z ∈ innerFieldTestAnnulus h <;> simp [innerFieldAnnulusWeight,hz])

lemma innerCapAverage_eq (G : CoreObservationGraph) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    G.innerCapAverage Z lam h =
      3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h*
        (∫ z in innerFieldTestAnnulus h, G.fieldMoment Z lam z)+
      3*lam^2*G.mass+3*(16*packetPotentialConstant)^2*G.weightedMoment (coulombTailWeight h) := by
  have he : G.innerCapAverage Z lam h =
      3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h*
        coreLawAverage G.vector (fun φ => ∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z φ)+
      3*lam^2*coreLawAverage G.vector formMass+
      3*(16*packetPotentialConstant)^2*G.weightedMoment (coulombTailWeight h) := by
    unfold innerCapAverage coreLawAverage innerCapStatistic weightedMoment coreLawAverage
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only
    have hA : Integrable (fun v => 3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h*
        (∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z (coreSlice G.vector t v))) :=
      (coreFieldSquare_annular_statistic_integrable G.sobolev t hZ hlam hh).const_mul _
    have hB : Integrable (fun v => 3*lam^2*formMass (coreSlice G.vector t v)) :=
      (G.sobolev.coreSlice_mass_integrable t).const_mul _
    have hC : Integrable (fun v => 3*(16*packetPotentialConstant)^2*
        rawWeightedMoment (coreSlice G.vector t v) (coulombTailWeight h)) :=
      (rawWeightedMoment_coreSlice_integrable G.sobolev (coulombTailWeight_measurable h)
        (coulombTailWeight_nonneg h) (coulombTailWeight_le hh) t).const_mul _
    have hAB := integral_add hA hB
    have hABC := integral_add (hA.add hB) hC
    simp only [Pi.add_apply] at hABC hAB
    rw [hABC,hAB]
    simp only [integral_const_mul]
  rw [he,coreFieldSquare_annular_fubini G.sobolev hZ hlam hh,coreLawAverage_mass G.sobolev]
  rfl
end CoreObservationGraph

namespace CoreObservationEnsemble

def innerCapAverage (E : CoreObservationEnsemble) (Z lam h : ℝ) : ℝ :=
  ∑ i, (E.graph i).innerCapAverage Z lam h

lemma fieldMoment_annular_integrable (E : CoreObservationEnsemble) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    IntegrableOn (E.fieldMoment Z lam) (innerFieldTestAnnulus h) :=
  integrable_finsetSum _ (fun i _ => (E.graph i).fieldMoment_annular_integrable hZ hlam hh)

lemma innerCapAverage_eq (E : CoreObservationEnsemble) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    E.innerCapAverage Z lam h =
      3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h*
        (∫ z in innerFieldTestAnnulus h, E.fieldMoment Z lam z)+
      3*lam^2*E.mass+3*(16*packetPotentialConstant)^2*E.weightedMoment (coulombTailWeight h) := by
  unfold innerCapAverage
  simp_rw [CoreObservationGraph.innerCapAverage_eq _ hZ hlam hh]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  unfold fieldMoment mass weightedMoment
  rw [integral_finsetSum _ (fun i _ => (E.graph i).fieldMoment_annular_integrable hZ hlam hh)]

lemma innerCapAverage_bound (E : CoreObservationEnsemble) {Z lam h F T : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) (hm : E.mass = 1)
    (hf : ∀ z ∈ innerFieldTestAnnulus h, E.fieldMoment Z lam z ≤ F)
    (ht : E.weightedMoment (coulombTailWeight h) ≤ T) :
    E.innerCapAverage Z lam h ≤
      3*(packetDensityConstant/(h/4)^3)^2*(innerFieldVolume h)^2*F+
      3*lam^2+3*(16*packetPotentialConstant)^2*T := by
  rw [innerCapAverage_eq E hZ hlam hh,hm,mul_one]
  have hI : (∫ z in innerFieldTestAnnulus h, E.fieldMoment Z lam z) ≤ innerFieldVolume h*F := by
    let : IsFiniteMeasure (volume.restrict (innerFieldTestAnnulus h)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact innerFieldTestAnnulus_finite h⟩
    have hb := integral_mono_ae (E.fieldMoment_annular_integrable hZ hlam hh)
      (integrable_const F) (ae_restrict_of_forall_mem (innerFieldTestAnnulus_measurable h) hf)
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,innerFieldVolume] using hb
  have hcoef : 0 ≤ 3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h := by
    have := innerFieldVolume_nonneg h; positivity
  calc
    _ ≤ 3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h*(innerFieldVolume h*F)+
        3*lam^2+3*(16*packetPotentialConstant)^2*T :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hI hcoef) le_rfl)
        (mul_le_mul_of_nonneg_left ht (by positivity))
    _ = _ := by ring
end CoreObservationEnsemble

end CoulombAtom

end

end OAI
