import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.TranslatedShortRange
import OAI.Analysis.CoulombIonization.FormDomain.FormRawPotential

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom

def rawOneParticleLaw {N : ℕ} (μ : Measure (Configuration N)) : Measure Space :=
  Measure.sum (fun i : Fin N => μ.map (fun x => x i))

lemma rawOneParticleLaw_finite {N : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] : IsFiniteMeasure (rawOneParticleLaw μ) := by
  rw [rawOneParticleLaw,Measure.sum_fintype]
  infer_instance

lemma rawOneParticleLaw_ac {N : ℕ} (ψ : FormVector N) :
    rawOneParticleLaw (formRawLaw ψ) ≪ volume := by
  apply Measure.absolutelyContinuous_sum_left
  intro i
  exact ((withDensity_absolutelyContinuous volume _).map (measurable_pi_apply i)).trans
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin N => (volume : Measure Space)) i).absolutelyContinuous

def ordinaryDensity {N : ℕ} (ψ : FormVector N) (z : Space) : ℝ :=
  ((rawOneParticleLaw (formRawLaw ψ)).rnDeriv volume z).toReal

lemma ordinaryDensity_nonneg {N : ℕ} (ψ : FormVector N) (z : Space) :
    0 ≤ ordinaryDensity ψ z := ENNReal.toReal_nonneg

lemma ordinaryDensity_measurable {N : ℕ} (ψ : FormVector N) :
    Measurable (ordinaryDensity ψ) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

lemma ordinaryDensity_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    Integrable (ordinaryDensity ψ) := by
  let : IsFiniteMeasure (formRawLaw ψ) := formRawLaw_finite hψ
  let : IsFiniteMeasure (rawOneParticleLaw (formRawLaw ψ)) := rawOneParticleLaw_finite _
  exact Measure.integrable_toReal_rnDeriv

lemma rawOneParticleLaw_pairing {N : ℕ} (μ : Measure (Configuration N))
    {f : Space → ℝ} (hf : Measurable f) (hi : ∀ i : Fin N, Integrable (fun x => f (x i)) μ) :
    (∫ z, f z ∂rawOneParticleLaw μ) = ∫ x, ∑ i, f (x i) ∂μ := by
  have him (i : Fin N) : Integrable f (μ.map (fun x => x i)) :=
    (integrable_map_measure hf.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).mpr (hi i)
  rw [rawOneParticleLaw,Measure.sum_fintype,integral_finsetSum_measure (fun i _ => him i),
    integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable

lemma ordinaryDensity_pairing {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {f : Space → ℝ} (hf : Measurable f)
    (hi : ∀ i : Fin N, Integrable (fun x => f (x i)) (formRawLaw ψ)) :
    (∫ z, ordinaryDensity ψ z*f z) = ∫ x, ∑ i, f (x i) ∂formRawLaw ψ := by
  let : IsFiniteMeasure (formRawLaw ψ) := formRawLaw_finite hψ
  let : IsFiniteMeasure (rawOneParticleLaw (formRawLaw ψ)) := rawOneParticleLaw_finite _
  change (∫ z, ((rawOneParticleLaw (formRawLaw ψ)).rnDeriv volume z).toReal*f z) = _
  rw [integral_toReal_rnDeriv_mul (rawOneParticleLaw_ac ψ)]
  exact rawOneParticleLaw_pairing _ hf hi

lemma ordinaryDensity_measure {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    volume.withDensity (fun z => ENNReal.ofReal (ordinaryDensity ψ z)) =
      rawOneParticleLaw (formRawLaw ψ) := by
  let : IsFiniteMeasure (formRawLaw ψ) := formRawLaw_finite hψ
  let : IsFiniteMeasure (rawOneParticleLaw (formRawLaw ψ)) := rawOneParticleLaw_finite _
  calc
    _ = volume.withDensity ((rawOneParticleLaw (formRawLaw ψ)).rnDeriv volume) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top (rawOneParticleLaw (formRawLaw ψ)) volume] with z hz
      exact ENNReal.ofReal_toReal hz.ne
    _ = _ := Measure.withDensity_rnDeriv_eq _ _ (rawOneParticleLaw_ac ψ)

lemma ordinaryDensity_mass {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    (∫ z, ordinaryDensity ψ z) = (N:ℝ)*formMass ψ := by
  let : IsFiniteMeasure (formRawLaw ψ) := formRawLaw_finite hψ
  have he := ordinaryDensity_pairing hψ (measurable_const (a := (1:ℝ)))
    (fun _ => integrable_const 1)
  simp only [mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
  rw [he,integral_const,smul_eq_mul,measureReal_def,formRawLaw_univ hψ,
    ENNReal.toReal_ofReal (formMass_nonneg ψ)]
  ring

lemma ordinaryDensity_raw_local_potential {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) (q : ℝ) :
    (∫ x, rawLocalPotential y q x ∂formRawLaw ψ) =
      ∫ z in ball y q, ordinaryDensity ψ z/‖z-y‖ := by
  let f : Space → ℝ := fun z => if ‖z-y‖ < q then 1/‖z-y‖ else 0
  have hf : Measurable f := Measurable.ite
    (measurableSet_lt ((continuous_id.sub continuous_const).norm.measurable) measurable_const)
    (measurable_const.div ((continuous_id.sub continuous_const).norm.measurable)) measurable_const
  have hn (z : Space) : 0 ≤ f z := by dsimp [f]; split_ifs <;> positivity
  have hi (i : Fin N) : Integrable (fun x : Configuration N => f (x i)) (formRawLaw ψ) := by
    apply (rawPotential_form_integrable hψ y).mono'
      (hf.comp (measurable_pi_apply i)).aestronglyMeasurable
    apply ae_of_all
    intro x
    change ‖f (x i)‖ ≤ rawPotential y x
    rw [Real.norm_of_nonneg (hn _)]
    have hle : 1/‖x i-y‖ ≤ rawPotential y x := by
      unfold rawPotential
      exact Finset.single_le_sum (f := fun j : Fin N => (1:ℝ)/‖x j-y‖)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    dsimp [f]
    split_ifs
    · exact hle
    · exact rawPotential_nonneg y x
  have hp := ordinaryDensity_pairing hψ hf hi
  have he : (fun z => ordinaryDensity ψ z*f z) =
      (ball y q).indicator (fun z => ordinaryDensity ψ z/‖z-y‖) := by
    funext z
    by_cases hz : ‖z-y‖ < q
    · have hm : z ∈ ball y q := by simpa only [mem_ball,dist_eq_norm] using hz
      rw [Set.indicator_of_mem hm]
      simp [f,hz,div_eq_mul_inv]
    · have hm : z ∉ ball y q := by simpa only [mem_ball,dist_eq_norm] using hz
      rw [Set.indicator_of_notMem hm]
      simp [f,hz]
  rw [he,integral_indicator measurableSet_ball] at hp
  exact hp.symm

theorem ordinaryDensity_raw_local_holder {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) {q : ℝ} (hq : 0 < q)
    (hp : MemLp (ordinaryDensity ψ) (5/3) (volume.restrict (ball y q))) :
    (∫ x, rawLocalPotential y q x ∂formRawLaw ψ) ≤
      (∫ z in ball y q, (ordinaryDensity ψ z)^(5/3:ℝ))^(3/5:ℝ)*
        (8*Real.pi)^(2/5:ℝ)*q^(1/5:ℝ) := by
  rw [ordinaryDensity_raw_local_potential hψ]
  have hh := CoulombAnalysis.coulomb_short_range_holder_centered hq y hp
  simpa only [Real.norm_of_nonneg (ordinaryDensity_nonneg ψ _),norm_sub_rev y] using hh

end CoulombAtom

end

end OAI
