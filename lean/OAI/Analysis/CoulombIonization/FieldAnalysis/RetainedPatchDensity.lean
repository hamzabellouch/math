import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedSmear
import OAI.Analysis.CoulombIonization.Variational.PatchTranslatedDensity

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis
variable {N : ℕ}

lemma retainedSmear_fixed_measurable (b : ℝ) (S : Finset (Fin N)) (x : Configuration N) :
    Measurable (retainedSmear b S x) := by
  unfold retainedSmear
  exact Finset.measurable_sum _ (fun i _ => (varthetaScaled_measurable b).comp
    (measurable_id.sub_const (x i)))

lemma retainedSmear_bound {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (z : Space) : retainedSmear b S x z ≤ S.card*b⁻¹^3 := by
  exact (Finset.sum_le_sum (fun i _ => varthetaScaled_le hb (z-x i))).trans_eq
    (by simp only [Finset.sum_const,nsmul_eq_mul])

lemma retainedSmear_zero_outside {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R)
    {z : Space} (hz : R ≤ ‖z-y‖) : retainedSmear b S x z = 0 := by
  apply retainedSmear_support hb
  intro i hi
  have hh : ‖z-y‖ ≤ ‖z-x i‖+‖x i-y‖ := by
    simpa only [dist_eq_norm] using dist_triangle z (x i) y
  linarith [hmargin i hi]

lemma retainedPatch_memLp {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (R : ℝ) :
    MemLp (fun z => retainedSmear b S x (y+z)) (5/3) (ballMeasure R) := by
  apply MemLp.of_bound
    (((retainedSmear_fixed_measurable b S x).comp (measurable_const.add measurable_id)).aestronglyMeasurable)
    (S.card*b⁻¹^3)
  exact Eventually.of_forall fun z => by
    change ‖retainedSmear b S x (y+z)‖ ≤ S.card*b⁻¹^3
    rw [Real.norm_of_nonneg (retainedSmear_nonneg hb S x _)]
    exact retainedSmear_bound hb S x _

def retainedPatchLp {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (R : ℝ) : TFLp (ballMeasure R) :=
  (retainedPatch_memLp hb S x y R).toLp (fun z => retainedSmear b S x (y+z))

lemma retainedPatchLp_ae {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (R : ℝ) :
    retainedPatchLp hb S x y R =ᵐ[ballMeasure R] fun z => retainedSmear b S x (y+z) :=
  (retainedPatch_memLp hb S x y R).coeFn_toLp

lemma retainedPatchLp_nonneg {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (R : ℝ) : NonnegDensity (retainedPatchLp hb S x y R) := by
  exact (retainedPatchLp_ae hb S x y R).mono fun z hz => hz.symm ▸ retainedSmear_nonneg hb S x _

lemma retainedPatchLp_bound {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (R : ℝ) :
    ∀ᵐ z ∂ballMeasure R, retainedPatchLp hb S x y R z ≤ S.card*b⁻¹^3 := by
  exact (retainedPatchLp_ae hb S x y R).mono fun z hz => hz.symm ▸ retainedSmear_bound hb S x _

lemma retainedPatchLp_extension {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    tfExtension R (retainedPatchLp hb S x y R) =ᵐ[volume] fun z => retainedSmear b S x (y+z) := by
  have hh := (ae_restrict_iff' measurableSet_ball).mp (retainedPatchLp_ae hb S x y R)
  filter_upwards [hh] with z hz
  by_cases hm : z ∈ ball (0:Space) R
  · simpa only [tfExtension,indicator_of_mem hm] using hz hm
  · rw [tfExtension,indicator_of_notMem hm]
    symm
    apply retainedSmear_zero_outside hb S x y hmargin
    simpa only [add_sub_cancel_left] using (not_lt.mp (by
      simpa only [mem_ball,dist_eq_norm,sub_zero] using hm : ¬‖z‖ < R))

lemma retainedPatch_density_ae {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    translatedPatchDensity y R (S.card*b⁻¹^3) (retainedPatchLp hb S x y R) =ᵐ[volume]
      retainedSmear b S x := by
  have he := (boundedPatchRepresentative_ae (retainedPatchLp_nonneg hb S x y R)
    (retainedPatchLp_bound hb S x y R)).trans (retainedPatchLp_extension hb S x y hmargin)
  have ht := (measurePreserving_add_left (volume : Measure Space) (-y)).quasiMeasurePreserving.ae he
  filter_upwards [ht] with z hz
  simpa only [translatedPatchDensity,add_neg_cancel_left] using hz

lemma retainedPatchLp_mass {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    (∫ z, retainedPatchLp hb S x y R z ∂ballMeasure R) = (S.card:ℝ) := by
  rw [←translatedPatchDensity_mass y (retainedPatchLp_nonneg hb S x y R)
    (retainedPatchLp_bound hb S x y R),integral_congr_ae (retainedPatch_density_ae hb S x y hmargin)]
  exact integral_retainedSmear hb S x

lemma retainedPatchLp_kinetic {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    ‖retainedPatchLp hb S x y R‖^(5/3:ℝ) = retainedPressure b S x := by
  rw [←translatedPatchDensity_kinetic y (retainedPatchLp_nonneg hb S x y R)
    (retainedPatchLp_bound hb S x y R)]
  exact integral_congr_ae ((retainedPatch_density_ae hb S x y hmargin).mono fun z hz => by dsimp only at *; rw [hz])

lemma retainedPatchLp_coulomb {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    tfCoulombL R (retainedPatchLp hb S x y R) (retainedPatchLp hb S x y R) =
      ∫ p : Space × Space, retainedSmear b S x p.1*retainedSmear b S x p.2/‖p.1-p.2‖ := by
  rw [←translatedPatchDensity_coulomb y (retainedPatchLp_nonneg hb S x y R)
    (retainedPatchLp_bound hb S x y R)]
  have he := retainedPatch_density_ae hb S x y hmargin
  apply integral_congr_ae
  rw [Measure.volume_eq_prod]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae he,
    Measure.quasiMeasurePreserving_snd.ae he] with p h1 h2
  rw [h1,h2]

lemma retainedPatchLp_field {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R)
    (Φ : Space → ℝ) :
    (∫ z, Φ (y+z)*retainedPatchLp hb S x y R z ∂ballMeasure R) =
      ∫ z, Φ z*retainedSmear b S x z := by
  rw [←translatedPatchDensity_field y (retainedPatchLp_nonneg hb S x y R)
    (retainedPatchLp_bound hb S x y R)]
  exact integral_congr_ae ((retainedPatch_density_ae hb S x y hmargin).mono fun z hz => by dsimp only at *; rw [hz])

lemma retainedPatchLp_functional {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R)
    (Φ : TFField R) (field : Space → ℝ) (hΦ : Φ =ᵐ[ballMeasure R] fun z => field (y+z)) (T : ℝ) :
    tfPatchFunctional R T Φ (retainedPatchLp hb S x y R) =
      T*retainedPressure b S x-(∫ z, field z*retainedSmear b S x z)+
      (1/2:ℝ)*(∫ p : Space × Space, retainedSmear b S x p.1*retainedSmear b S x p.2/‖p.1-p.2‖) := by
  rw [tfPatchFunctional,tfPatchLinear_apply,retainedPatchLp_kinetic hb S x y hmargin,
    retainedPatchLp_coulomb hb S x y hmargin]
  have he : (∫ z, Φ z*retainedPatchLp hb S x y R z ∂ballMeasure R) =
      ∫ z, field (y+z)*retainedPatchLp hb S x y R z ∂ballMeasure R :=
    integral_congr_ae (hΦ.mono fun z hz => by dsimp only at *; rw [hz])
  rw [he,retainedPatchLp_field hb S x y hmargin]
  ring

end CoulombNeumann

end

end OAI
