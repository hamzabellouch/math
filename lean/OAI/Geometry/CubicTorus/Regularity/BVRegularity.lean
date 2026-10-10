import Mathlib
import OAI.Geometry.CubicTorus.Model

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

end CubicTorus

namespace CubicTorus

lemma continuous_quotientMap : Continuous quotientMap := by
  unfold quotientMap
  fun_prop

lemma measurable_quotientMap : Measurable quotientMap := continuous_quotientMap.measurable

lemma measurableSet_fundamentalCube : MeasurableSet fundamentalCube := by
  unfold fundamentalCube
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have hm : Measurable (fun x : Cover => x i) := by fun_prop
  exact (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)

lemma volume_fundamentalCube : volume fundamentalCube = 1 := by
  have hm := (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage measurableSet_fundamentalCube.nullMeasurableSet
  have heq : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
      Set.pi univ (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
    ext x
    simp [fundamentalCube]
  rw [heq] at hm
  have hv : volume (Set.pi univ (fun _ : Fin 3 => Ico (0 : ℝ) 1)) = 1 := by
    rw [Real.volume_pi_Ico]
    norm_num
  exact hm.symm.trans hv

lemma torusVolume_univ : torusVolume univ = 1 := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap MeasurableSet.univ]
  simp [volume_fundamentalCube]

instance : IsProbabilityMeasure torusVolume := ⟨torusVolume_univ⟩

lemma admissible_zero : AdmissibleField (fun _ => 0) := by
  exact ⟨contDiff_const, by simp, by simp⟩

lemma divergence_zero (x : Cover) : divergence (fun _ => 0) x = 0 := by
  simp [divergence]

lemma admissible_neg {F : Cover → Cover} (hF : AdmissibleField F) :
    AdmissibleField (fun x => -F x) := by
  refine ⟨hF.1.neg, ?_, ?_⟩
  · intro n x
    change -F (x + latticeVector n) = -F x
    rw [hF.2.1 n x]
  · intro x
    simpa using hF.2.2 x

lemma divergence_neg (F : Cover → Cover) (x : Cover) :
    divergence (fun x => -F x) x = -divergence F x := by
  unfold divergence
  change ∑ i : Fin 3, (fderiv ℝ (-F) x (EuclideanSpace.single i 1)) i = _
  rw [fderiv_neg]
  simp

lemma perimeter_empty : perimeter ∅ = 0 := by
  simp [perimeter]

lemma finitePerimeter_empty : FinitePerimeter ∅ := by
  simp [FinitePerimeter, perimeter_empty]

lemma liftSet_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    (fundamentalCube ∩ quotientMap ⁻¹' E : Set Cover) =ᵐ[volume]
      (fundamentalCube ∩ quotientMap ⁻¹' F : Set Cover) := by
  have hh := ae_of_ae_map measurable_quotientMap.aemeasurable hEF
  have h := (ae_restrict_iff' measurableSet_fundamentalCube).1 hh
  filter_upwards [h] with x hx
  change (x ∈ fundamentalCube ∧ quotientMap x ∈ E) =
    (x ∈ fundamentalCube ∧ quotientMap x ∈ F)
  by_cases hc : x ∈ fundamentalCube
  · have hh : (quotientMap x ∈ E) = (quotientMap x ∈ F) := hx hc
    simpa only [hc, true_and] using hh
  · simp only [hc, false_and]

theorem perimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    perimeter E = perimeter F := by
  unfold perimeter
  apply iSup_congr
  intro X
  apply iSup_congr
  intro _
  rw [setIntegral_congr_set (liftSet_congr_ae hEF)]

theorem finitePerimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    FinitePerimeter E ↔ FinitePerimeter F := by
  rw [FinitePerimeter, FinitePerimeter, perimeter_congr_ae hEF]
  exact and_congr ⟨fun h => h.congr hEF, fun h => h.congr hEF.symm⟩ Iff.rfl

theorem isMinimizerAt_congr_ae {E F : Set Torus} {V : ℝ}
    (hEF : E =ᵐ[torusVolume] F) : IsMinimizerAt V E ↔ IsMinimizerAt V F := by
  unfold IsMinimizerAt
  rw [finitePerimeter_congr_ae hEF, measure_congr hEF, perimeter_congr_ae hEF]

lemma continuous_divergence {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (divergence F) := by
  unfold divergence
  apply continuous_finsetSum
  intro i _
  exact (EuclideanSpace.proj i).continuous.comp
    ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

lemma integrableOn_divergence {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    IntegrableOn (divergence F) fundamentalCube := by
  have hEmb := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toHomeomorph.measurableEmbedding
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integrableOn_comp_preimage hEmb]
  rw [cube_preimage]
  have hc : Continuous (fun x : Fin 3 → ℝ => divergence F (WithLp.toLp 2 x)) :=
    (continuous_divergence hF).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous
  apply hc.integrableOn_Icc.mono_set
  intro x hx
  exact ⟨fun i => (hx i (mem_univ i)).1, fun i => le_of_lt (hx i (mem_univ i)).2⟩

lemma adjacent_faces {i : Fin 3} (x : Fin 2 → ℝ) :
    WithLp.toLp 2 (i.insertNth 1 x) =
      (WithLp.toLp 2 (i.insertNth 0 x) : Cover) + latticeVector (Pi.single i 1) := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [latticeVector]
  · simp [latticeVector, Fin.succAbove_ne i k]

theorem integral_divergence_fundamentalCube {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube, divergence F x) = 0 := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  let g : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i x => F (e.symm x) i
  let dg : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun i x => (EuclideanSpace.proj i).comp
      ((fderiv ℝ F (e.symm x)).comp e.symm.toContinuousLinearMap)
  have hdg : ∀ i x, HasFDerivAt (g i) (dg i x) x := by
    intro i x
    exact (EuclideanSpace.proj i).hasFDerivAt.comp x
      (((hF.1.differentiable (by simp)) (e.symm x)).hasFDerivAt.comp x e.symm.hasFDerivAt)
  have hd : (fun x => ∑ i : Fin 3, dg i x (Pi.single i 1)) =
      fun x => divergence F (e.symm x) := by
    funext x
    simp [dg, divergence, e, PiLp.toLp_single]
  have hct : Continuous (fun x => divergence F (e.symm x)) :=
    (continuous_divergence hF.1).comp e.symm.continuous
  have hth := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin 3 → ℝ) (1 : Fin 3 → ℝ) (by intro i; norm_num)
    g dg ∅ countable_empty
    (fun i => ((EuclideanSpace.proj i).continuous.comp
      (hF.1.continuous.comp e.symm.continuous)).continuousOn)
    (fun x _ i => hdg i x) (by rw [hd]; exact hct.integrableOn_Icc)
  rw [hd] at hth
  have hzero : (∑ i : Fin 3,
      ((∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) ((1 : Fin 3 → ℝ) ∘ i.succAbove),
         g i (i.insertNth 1 x)) -
       ∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) ((1 : Fin 3 → ℝ) ∘ i.succAbove),
         g i (i.insertNth 0 x))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have heq : (fun x : Fin 2 → ℝ => g i (i.insertNth 1 x)) =
        (fun x : Fin 2 → ℝ => g i (i.insertNth 0 x)) := by
      funext x
      change F (WithLp.toLp 2 (i.insertNth 1 x)) i = F (WithLp.toLp 2 (i.insertNth 0 x)) i
      rw [adjacent_faces, hF.2.1]
    rw [heq, sub_self]
  have hi : (∫ x in Icc (0 : Fin 3 → ℝ) 1, divergence F (e.symm x)) = 0 := hth.trans hzero
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    e.symm.toHomeomorph.measurableEmbedding, cube_preimage]
  rw [volume_pi, setIntegral_congr_set Measure.univ_pi_Ico_ae_eq_Icc]
  exact hi

lemma quotientMap_measurePreserving :
    MeasurePreserving quotientMap (volume.restrict fundamentalCube) torusVolume :=
  ⟨measurable_quotientMap, rfl⟩

lemma integral_divergence_compl {E : Set Torus} (hE : NullMeasurableSet E torusVolume)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' Eᶜ, divergence F x) =
      -(∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) := by
  have hm := hE.preimage quotientMap_measurePreserving.quasiMeasurePreserving
  have hi := integral_add_compl₀ hm (integrableOn_divergence hF.1)
  rw [Measure.restrict_restrict₀ hm, Measure.restrict_restrict₀ hm.compl,
    integral_divergence_fundamentalCube hF] at hi
  simp only [inter_comm] at hi
  rw [preimage_compl]
  linarith

theorem perimeter_compl {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    perimeter Eᶜ = perimeter E := by
  have hle : ∀ E : Set Torus, NullMeasurableSet E torusVolume →
      perimeter Eᶜ ≤ perimeter E := by
    intro E hE
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply le_iSup_of_le (fun x => -F x)
    apply le_iSup_of_le (admissible_neg hF)
    rw [integral_divergence_compl hE hF]
    simp only [divergence_neg, integral_neg, le_refl]
  exact le_antisymm (hle E hE) (by simpa only [compl_compl] using hle Eᶜ hE.compl)

theorem finitePerimeter_compl {E : Set Torus} :
    FinitePerimeter Eᶜ ↔ FinitePerimeter E := by
  constructor
  · rintro ⟨hm, hp⟩
    have hm' : NullMeasurableSet E torusVolume := by simpa using hm.compl
    exact ⟨hm', by simpa only [perimeter_compl hm'] using hp⟩
  · rintro ⟨hm, hp⟩
    exact ⟨hm.compl, by rwa [perimeter_compl hm]⟩

def characteristic (E : Set Torus) (x : Torus) : ℝ := E.indicator (fun _ => 1) x

lemma lift_indicator_integral {E : Set Torus} (hE : NullMeasurableSet E torusVolume)
    (g : Cover → ℝ) :
    (∫ x in fundamentalCube, (quotientMap ⁻¹' E).indicator g x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, g x := by
  have hm := hE.preimage quotientMap_measurePreserving.quasiMeasurePreserving
  rw [integral_indicator₀ hm, Measure.restrict_restrict₀ hm, inter_comm]

lemma characteristic_mul (E : Set Torus) (g : Cover → ℝ) (x : Cover) :
    characteristic E (quotientMap x) * g x = (quotientMap ⁻¹' E).indicator g x := by
  classical
  by_cases hx : quotientMap x ∈ E <;> simp [characteristic, hx]

theorem tendsto_lift_integral {Es : ℕ → Set Torus} {E : Set Torus}
    (hEs : ∀ n, NullMeasurableSet (Es n) torusVolume)
    (hE : NullMeasurableSet E torusVolume)
    (hlim : ∀ᵐ x ∂torusVolume,
      Filter.Tendsto (fun n => characteristic (Es n) x) Filter.atTop
        (nhds (characteristic E x)))
    {g : Cover → ℝ} (hg : IntegrableOn g fundamentalCube) :
    Filter.Tendsto
      (fun n => ∫ x in fundamentalCube ∩ quotientMap ⁻¹' Es n, g x)
      Filter.atTop (nhds (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, g x)) := by
  have hms (n : ℕ) := (hEs n).preimage quotientMap_measurePreserving.quasiMeasurePreserving
  have hlift := ae_of_ae_map measurable_quotientMap.aemeasurable hlim
  have hconv : ∀ᵐ x ∂volume.restrict fundamentalCube,
      Filter.Tendsto (fun n => (quotientMap ⁻¹' Es n).indicator g x)
        Filter.atTop (nhds ((quotientMap ⁻¹' E).indicator g x)) := by
    filter_upwards [hlift] with x hx
    simpa only [characteristic_mul] using hx.mul_const (g x)
  have hdom := tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
    (fun n => (hg.indicator₀ (hms n)).aestronglyMeasurable) hg.norm
    (fun n => Filter.Eventually.of_forall (fun x => norm_indicator_le_norm_self _ _)) hconv
  simpa only [lift_indicator_integral hE, lift_indicator_integral (hEs _)] using hdom

theorem perimeter_le_of_ae_tendsto {Es : ℕ → Set Torus} {E : Set Torus} {L : ℝ≥0∞}
    (hEs : ∀ n, NullMeasurableSet (Es n) torusVolume)
    (hE : NullMeasurableSet E torusVolume)
    (hlim : ∀ᵐ x ∂torusVolume,
      Filter.Tendsto (fun n => characteristic (Es n) x) Filter.atTop
        (nhds (characteristic E x)))
    (hbound : ∀ n, perimeter (Es n) ≤ L) : perimeter E ≤ L := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have ht := tendsto_lift_integral hEs hE hlim (integrableOn_divergence hF.1)
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht)
  apply Filter.Eventually.of_forall
  intro n
  change ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' Es n, divergence F x) ≤ L
  exact (le_iSup₂ (f := fun F (_ : AdmissibleField F) =>
    ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' Es n, divergence F x)) F hF).trans (hbound n)

lemma integral_characteristic {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    (∫ x, characteristic E x ∂torusVolume) = (torusVolume E).toReal := by
  unfold characteristic
  rw [integral_indicator₀ hE, setIntegral_const]
  simp [Measure.real_def]

theorem tendsto_volume_of_ae_tendsto {Es : ℕ → Set Torus} {E : Set Torus}
    (hEs : ∀ n, NullMeasurableSet (Es n) torusVolume)
    (hE : NullMeasurableSet E torusVolume)
    (hlim : ∀ᵐ x ∂torusVolume,
      Filter.Tendsto (fun n => characteristic (Es n) x) Filter.atTop
        (nhds (characteristic E x))) :
    Filter.Tendsto (fun n => torusVolume (Es n)) Filter.atTop (nhds (torusVolume E)) := by
  have hconv := tendsto_integral_of_dominated_convergence (fun _ : Torus => (1 : ℝ))
    (fun n => ((integrable_const (1 : ℝ)).indicator₀ (hEs n)).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n => Filter.Eventually.of_forall (fun x => by
      change ‖(Es n).indicator (fun _ => (1 : ℝ)) x‖ ≤ 1
      simpa only [norm_one] using norm_indicator_le_norm_self (s := Es n) (fun _ => (1 : ℝ)) x))
    hlim
  change Filter.Tendsto (fun n => ∫ x, characteristic (Es n) x ∂torusVolume)
    Filter.atTop (nhds (∫ x, characteristic E x ∂torusVolume)) at hconv
  simp only [integral_characteristic (hEs _), integral_characteristic hE] at hconv
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hconv
  simpa only [Function.comp_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

lemma volume_compl_of_volume {E : Set Torus} {V : ℝ}
    (hE : NullMeasurableSet E torusVolume) (hV : 0 ≤ V)
    (hvolume : torusVolume E = ENNReal.ofReal V) :
    torusVolume Eᶜ = ENNReal.ofReal (1 - V) := by
  rw [measure_compl₀ hE (measure_ne_top _ _), torusVolume_univ, hvolume,
    ENNReal.ofReal_sub 1 hV, ENNReal.ofReal_one]

theorem isMinimizerAt_compl {V : ℝ} (hV : V ∈ Icc 0 1) {E : Set Torus} :
    IsMinimizerAt (1 - V) Eᶜ ↔ IsMinimizerAt V E := by
  have hforward : ∀ V : ℝ, V ∈ Icc 0 1 → ∀ E : Set Torus,
      IsMinimizerAt V E → IsMinimizerAt (1 - V) Eᶜ := by
    intro V hV E ⟨hE, hvolume, hmin⟩
    refine ⟨finitePerimeter_compl.mpr hE, volume_compl_of_volume hE.1 hV.1 hvolume, ?_⟩
    intro F hF hFvolume
    have hFcvolume : torusVolume Fᶜ = ENNReal.ofReal V := by
      have hh := volume_compl_of_volume hF.1 (sub_nonneg.mpr hV.2) hFvolume
      simpa only [sub_sub_cancel] using hh
    have hm := hmin Fᶜ (finitePerimeter_compl.mpr hF) hFcvolume
    rwa [perimeter_compl hE.1, perimeter_compl hF.1] at *
  constructor
  · intro h
    have hv : 1 - V ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr hV.2, by linarith [hV.1]⟩
    simpa only [sub_sub_cancel, compl_compl] using hforward (1 - V) hv Eᶜ h
  · exact hforward V hV E

theorem perimeter_le_of_ae_tendsto_bound {Es : ℕ → Set Torus} {E : Set Torus}
    {Ls : ℕ → ℝ≥0∞} {L : ℝ≥0∞}
    (hEs : ∀ n, NullMeasurableSet (Es n) torusVolume)
    (hE : NullMeasurableSet E torusVolume)
    (hlim : ∀ᵐ x ∂torusVolume,
      Filter.Tendsto (fun n => characteristic (Es n) x) Filter.atTop
        (nhds (characteristic E x)))
    (hbound : ∀ n, perimeter (Es n) ≤ Ls n)
    (hL : Filter.Tendsto Ls Filter.atTop (nhds L)) : perimeter E ≤ L := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_lift_integral hEs hE hlim (integrableOn_divergence hF.1))
  apply le_of_tendsto_of_tendsto ht hL
  apply Filter.Eventually.of_forall
  intro n
  exact (le_iSup₂ (f := fun F (_ : AdmissibleField F) =>
    ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' Es n, divergence F x)) F hF).trans (hbound n)

end CubicTorus

namespace CubicTorus

abbrev ProductTorus := Fin 3 → AddCircle (1 : ℝ)

lemma circle_measurePreserving_mk_Ico :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Ico 0 1)) volume := by
  rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

lemma torusVolume_eq_product :
    torusVolume = Measure.map (WithLp.toLp 2 : ProductTorus → Torus) volume := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  have he := (PiLp.volume_preserving_toLp (Fin 3)).restrict_preimage measurableSet_fundamentalCube
  rw [cube_preimage] at he
  have hp := measurePreserving_pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ))))
    (fun _ => circle_measurePreserving_mk_Ico)
  have hs : (volume : Measure (Fin 3 → ℝ)).restrict
      (univ.pi (fun _ : Fin 3 => Ico 0 1)) =
      Measure.pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hto : Measurable (WithLp.toLp 2 : ProductTorus → Torus) :=
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable
  unfold torusVolume
  rw [← he.map_eq, hs, Measure.map_map measurable_quotientMap (PiLp.volume_preserving_toLp (Fin 3)).measurable]
  rw [volume_pi, ← hp.map_eq, Measure.map_map hto hp.measurable]
  rfl

lemma product_to_torus_measurePreserving :
    MeasurePreserving (WithLp.toLp 2 : ProductTorus → Torus) volume torusVolume :=
  ⟨(PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable,
    torusVolume_eq_product.symm⟩

lemma torus_to_product_measurePreserving :
    MeasurePreserving (WithLp.ofLp : Torus → ProductTorus) torusVolume volume := by
  exact product_to_torus_measurePreserving.symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.toMeasurableEquiv

instance circle_probability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
  constructor
  simp

lemma torus_coordinate_measurePreserving (i : Fin 3) :
    MeasurePreserving (fun x : Torus => x i) torusVolume volume := by
  exact (measurePreserving_eval (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ)))) i).comp
    torus_to_product_measurePreserving

lemma measurableSet_canonicalSlab (V : ℝ) : MeasurableSet (canonicalSlab V) := by
  exact measurableSet_lt (by fun_prop) measurable_const

lemma volume_canonicalSlab {V : ℝ} (hV : V ∈ Icc 0 1) :
    torusVolume (canonicalSlab V) = ENNReal.ofReal V := by
  have heq : canonicalSlab V = (fun x : Torus => x 0) ⁻¹' Metric.ball 0 (V / 2) := by
    ext x
    simp [canonicalSlab, Metric.mem_ball, dist_zero_right]
  rw [heq, (torus_coordinate_measurePreserving 0).measure_preimage measurableSet_ball.nullMeasurableSet]
  rw [← measure_congr AddCircle.closedBall_ae_eq_ball, AddCircle.volume_closedBall]
  congr 1
  rw [min_eq_right (by linarith [hV.2] : 2 * (V / 2) ≤ 1)]
  ring

end CubicTorus

namespace CubicTorus

instance torusVolume_haar : torusVolume.IsAddHaarMeasure := by
  rw [torusVolume_eq_product]
  exact AddEquiv.isAddHaarMeasure_map volume (WithLp.addEquiv 2 ProductTorus).symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.continuous
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).continuous

lemma quotientMap_add (x y : Cover) : quotientMap (x + y) = quotientMap x + quotientMap y := by
  ext i
  simp [quotientMap]

lemma quotientMap_neg (x : Cover) : quotientMap (-x) = -quotientMap x := by
  ext i
  simp [quotientMap]

def representative (x : Torus) : Cover :=
  WithLp.toLp 2 (fun i => ((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ))

lemma measurable_representative : Measurable representative := by
  apply (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm.measurable.comp
  apply Measurable.of_eval
  intro i
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (by fun_prop))

lemma quotientMap_representative (x : Torus) : quotientMap (representative x) = x := by
  ext i
  simp [quotientMap, representative]

lemma quotientMap_surjective : Function.Surjective quotientMap :=
  fun x => ⟨representative x, quotientMap_representative x⟩

lemma same_quotient_lattice {x y : Cover} (h : quotientMap x = quotientMap y) :
    ∃ n : Fin 3 → ℤ, x = y + latticeVector n := by
  have hh : ∀ i : Fin 3, ∃ n : ℤ, (n : ℝ) = x i - y i := by
    intro i
    have hi : ((x i - y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      have he := congrArg (fun z : Torus => z i) h
      simpa [quotientMap, AddCircle.coe_sub] using sub_eq_zero.mpr he
    simpa only [zsmul_eq_mul, mul_one] using ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi)
  choose n hn using hh
  refine ⟨n, ?_⟩
  ext i
  simp only [PiLp.add_apply, latticeVector]
  linarith [hn i]

lemma periodic_representative {Y : Type*} {f : Cover → Y}
    (hf : ∀ n x, f (x + latticeVector n) = f x) (x : Cover) :
    f (representative (quotientMap x)) = f x := by
  obtain ⟨n, hn⟩ := same_quotient_lattice (quotientMap_representative (quotientMap x))
  rw [hn, hf]

lemma divergence_translate (F : Cover → Cover) (a x : Cover) :
    divergence (fun y => F (y + a)) x = divergence F (x + a) := by
  simp only [divergence, fderiv_comp_add_right]

lemma divergence_periodic {F : Cover → Cover}
    (hf : ∀ n x, F (x + latticeVector n) = F x) (n : Fin 3 → ℤ) (x : Cover) :
    divergence F (x + latticeVector n) = divergence F x := by
  have he : (fun y : Cover => F (y + latticeVector n)) = F := funext (hf n)
  rw [← divergence_translate, he]

lemma admissible_translate {F : Cover → Cover} (hF : AdmissibleField F) (a : Cover) :
    AdmissibleField (fun x => F (x + a)) := by
  refine ⟨hF.1.comp (contDiff_id.add contDiff_const), ?_, fun x => hF.2.2 _⟩
  intro n x
  change F ((x + latticeVector n) + a) = F (x + a)
  rw [add_right_comm, hF.2.1]

lemma setIntegral_lift {f : Cover → ℝ} (hf : Continuous f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ z in E, f (representative z) ∂torusVolume) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, f x := by
  calc
    _ = ∫ x in quotientMap ⁻¹' E, f (representative (quotientMap x))
        ∂volume.restrict fundamentalCube :=
      setIntegral_map hE (hf.measurable.comp measurable_representative).aestronglyMeasurable
        measurable_quotientMap.aemeasurable
    _ = _ := by
      simp_rw [periodic_representative hp]
      rw [Measure.restrict_restrict (measurable_quotientMap hE), inter_comm]

lemma flux_translation {F : Cover → Cover} (hF : AdmissibleField F)
    (a : Cover) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' ((fun z => z + quotientMap a) ⁻¹' E),
      divergence F x) =
    ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence (fun y => F (y - a)) x := by
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap a) ⁻¹' E) := by
    exact (by fun_prop : Measurable (fun z : Torus => z + quotientMap a)) hE
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) hpre]
  have hG := admissible_translate hF (-a)
  have hG' : AdmissibleField (fun y => F (y - a)) := by simpa [sub_eq_add_neg] using hG
  rw [← setIntegral_lift (continuous_divergence hG'.1) (divergence_periodic hG'.2.1) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (fun y => F (y - a)) (representative (z + quotientMap a))) := by
    funext z
    simp only [sub_eq_add_neg, divergence_translate]
    have hq : quotientMap (representative (z + quotientMap a) + -a) =
        quotientMap (representative z) := by
      rw [quotientMap_add, quotientMap_representative, quotientMap_representative,
        quotientMap_neg]
      abel
    obtain ⟨n, hn⟩ := same_quotient_lattice hq
    rw [hn, divergence_periodic hF.2.1]
  rw [he]
  exact (measurePreserving_add_right torusVolume (quotientMap a)).setIntegral_preimage_emb
    (Homeomorph.addRight (quotientMap a)).measurableEmbedding
      (fun z => divergence (fun y => F (y - a)) (representative z)) E

end CubicTorus

namespace CubicTorus

lemma perimeter_translation_le {E : Set Torus} (hE : MeasurableSet E) (a : Cover) :
    perimeter ((fun z => z + quotientMap a) ⁻¹' E) ≤ perimeter E := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [flux_translation hF a hE]
  have hG : AdmissibleField (fun y => F (y - a)) := by
    simpa [sub_eq_add_neg] using admissible_translate hF (-a)
  exact le_iSup_of_le (fun y => F (y - a)) (le_iSup_of_le hG le_rfl)

lemma perimeter_translation_measurable {E : Set Torus} (hE : MeasurableSet E) (a : Torus) :
    perimeter ((fun z => z + a) ⁻¹' E) = perimeter E := by
  obtain ⟨b, rfl⟩ := quotientMap_surjective a
  refine le_antisymm (perimeter_translation_le hE b) ?_
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap b) ⁻¹' E) :=
    (continuous_add_const _).measurable hE
  have hh := perimeter_translation_le hpre (-b)
  have he : (fun z : Torus => z + quotientMap (-b)) ⁻¹'
      ((fun z : Torus => z + quotientMap b) ⁻¹' E) = E := by
    ext z
    simp [quotientMap_neg]
  rwa [he] at hh

theorem perimeter_translation {E : Set Torus} (hE : NullMeasurableSet E torusVolume) (a : Torus) :
    perimeter ((fun z => z + a) ⁻¹' E) = perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := (measurePreserving_add_right torusVolume a).quasiMeasurePreserving.preimage_ae_eq he
  rw [← perimeter_congr_ae hp, ← perimeter_congr_ae he]
  exact perimeter_translation_measurable (measurableSet_toMeasurable _ _) a

lemma volume_translation {E : Set Torus} (hE : NullMeasurableSet E torusVolume) (a : Torus) :
    torusVolume ((fun z => z + a) ⁻¹' E) = torusVolume E :=
  (measurePreserving_add_right torusVolume a).measure_preimage hE

lemma finitePerimeter_translation {E : Set Torus} (hE : FinitePerimeter E) (a : Torus) :
    FinitePerimeter ((fun z => z + a) ⁻¹' E) := by
  refine ⟨hE.1.preimage (measurePreserving_add_right torusVolume a).quasiMeasurePreserving, ?_⟩
  rw [perimeter_translation hE.1]
  exact hE.2

theorem isMinimizerAt_translation {E : Set Torus} {V : ℝ} (hE : IsMinimizerAt V E) (a : Torus) :
    IsMinimizerAt V ((fun z => z + a) ⁻¹' E) := by
  refine ⟨finitePerimeter_translation hE.1 a, ?_, ?_⟩
  · rw [volume_translation hE.1.1, hE.2.1]
  · intro F hF hvF
    rw [perimeter_translation hE.1.1]
    exact hE.2.2 F hF hvF

end CubicTorus

namespace CubicTorus

lemma divergence_smul_const {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (a : Cover) :
    divergence (fun y => f y • a) point = fderiv ℝ f point a := by
  have ha : (∑ i : Fin 3, a i • EuclideanSpace.single i 1) = a := by
    ext j
    simp [Pi.single_apply]
  simp only [divergence, fderiv_smul_const hf, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, smul_eq_mul]
  conv_rhs => rw [← ha, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

lemma divergence_const_smul {F : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (c : ℝ) :
    divergence (fun y => c • F y) point = c * divergence F point := by
  change (∑ i : Fin 3, (fderiv ℝ (c • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_const_smul hF c]
  simp [divergence, Finset.mul_sum]

lemma abs_flux_le_perimeter {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x| ≤ (perimeter E).toReal := by
  apply abs_le.mpr
  constructor
  · have hh : ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        divergence (fun y => -F y) x) ≤ perimeter E :=
      le_iSup_of_le (fun y => -F y) (le_iSup_of_le (admissible_neg hF) le_rfl)
    simp_rw [divergence_neg, integral_neg] at hh
    have := (ENNReal.ofReal_le_iff_le_toReal hE).mp hh
    linarith
  · exact (ENNReal.ofReal_le_iff_le_toReal hE).mp
      (le_iSup_of_le F (le_iSup_of_le hF le_rfl))

lemma abs_flux_le_mul_perimeter {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x)
    {k : ℝ} (hk : 0 < k) (hb : ∀ x, ‖F x‖ ≤ k) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x| ≤ k * (perimeter E).toReal := by
  have hG : AdmissibleField (fun x => k⁻¹ • F x) := by
    refine ⟨hF.const_smul (k⁻¹ : ℝ), ?_, ?_⟩
    · intro n x
      change k⁻¹ • F (x + latticeVector n) = k⁻¹ • F x
      rw [hp]
    · intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
      calc
        k⁻¹ * ‖F x‖ ≤ k⁻¹ * k := mul_le_mul_of_nonneg_left (hb x) (by positivity)
        _ = 1 := inv_mul_cancel₀ hk.ne'
  have hg := abs_flux_le_perimeter hE hG
  simp_rw [divergence_const_smul (hF.differentiable (by simp)).differentiableAt,
    integral_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hk)] at hg
  calc
    _ = k * (k⁻¹ * |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x|) := by
      rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hg hk.le

end CubicTorus

namespace CubicTorus

lemma periodic_bounded {Y : Type*} [SeminormedAddGroup Y] {f : Cover → Y}
    (hf : Continuous f) (hp : ∀ n x, f (x + latticeVector n) = f x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  let K : Set Cover := (WithLp.toLp 2) '' (Icc (0 : Fin 3 → ℝ) 1)
  have hK : IsCompact K := isCompact_Icc.image (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  rw [← periodic_representative hp x]
  apply (hM _ ?_).trans (le_max_left _ _)
  refine ⟨fun i => ((AddCircle.equivIco (1 : ℝ) 0) (quotientMap x i) : ℝ), ?_, rfl⟩
  constructor
  · intro i
    exact ((AddCircle.equivIco (1 : ℝ) 0) (quotientMap x i)).property.1
  · intro i
    exact le_of_lt (by simpa using ((AddCircle.equivIco (1 : ℝ) 0) (quotientMap x i)).property.2)

lemma fderiv_periodic {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Cover → Y} (hp : ∀ n x, f (x + latticeVector n) = f x)
    (n : Fin 3 → ℤ) (x : Cover) :
    fderiv ℝ f (x + latticeVector n) = fderiv ℝ f x := by
  rw [← fderiv_comp_add_right (latticeVector n)]
  exact congrArg (fun g : Cover → Y => fderiv ℝ g x) (funext (hp n))

instance finiteMeasure_liftSet (E : Set Torus) :
    IsFiniteMeasure (volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)) := by
  apply isFiniteMeasure_restrict.mpr
  apply ne_of_lt
  apply lt_of_le_of_lt (measure_mono inter_subset_left)
  rw [volume_fundamentalCube]
  exact ENNReal.one_lt_top

lemma abs_directional_flux_le {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    (hb : ∀ x, |f x| ≤ 1) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f x a|
      ≤ ‖a‖ * (perimeter E).toReal := by
  by_cases ha : a = 0
  · simp [ha]
  have hd := hf.differentiable (by simp)
  have hfield : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x • a) := hf.smul_const a
  have hfieldp : ∀ n x, f (x + latticeVector n) • a = f x • a := by
    intro n x
    rw [hp]
  have hfieldb : ∀ x, ‖f x • a‖ ≤ ‖a‖ := by
    intro x
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg a) (hb x)
  simpa only [divergence_smul_const hd.differentiableAt] using
    abs_flux_le_mul_perimeter hE hfield hfieldp (norm_pos_iff.mpr ha) hfieldb

end CubicTorus

namespace CubicTorus

theorem smooth_test_translation_bound {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    (hb : ∀ x, |f x| ≤ 1) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (f (x + a) - f x)|
      ≤ ‖a‖ * (perimeter E).toReal := by
  have hdc := hf.continuous_fderiv (by simp)
  have hd := hf.differentiable (by simp)
  have hderiv (x t) : HasDerivAt (fun s : ℝ => f (x + s • a))
      (fderiv ℝ f (x + t • a) a) t := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, one_smul, zero_add] using
      (hd (x + t • a)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const a))
  have hFTC (x : Cover) : (∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • a) a)
      = f (x + a) - f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • a) a) :=
      (hdc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv x t) (hc.intervalIntegrable 0 1)
  obtain ⟨M, _, hM⟩ := periodic_bounded hdc (fderiv_periodic hp)
  have hc : Continuous (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a) :=
    (hdc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hi : Integrable (fun z : Cover × ℝ => fderiv ℝ f (z.1 + z.2 • a) a)
      ((volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (M * ‖a‖)
    exact Filter.Eventually.of_forall fun z =>
      ((fderiv ℝ f (z.1 + z.2 • a)).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg a))
  have ht (t : ℝ) : |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      fderiv ℝ f (x + t • a) a| ≤ ‖a‖ * (perimeter E).toReal := by
    have hp' : ∀ n x, f ((x + latticeVector n) + t • a) = f (x + t • a) := by
      intro n x
      rw [add_right_comm, hp]
    simpa only [Function.comp_def, id_eq, fderiv_comp_add_right] using
      abs_directional_flux_le hE (hf.comp (contDiff_id.add contDiff_const)) hp'
        (fun x => hb (x + t • a)) a
  calc
    _ = ‖∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        ∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (x + t • a) a‖ := by
      simp_rw [hFTC, Real.norm_eq_abs]
    _ = ‖∫ t in Ioc (0 : ℝ) 1,
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, fderiv ℝ f (x + t • a) a‖ := by
      rw [integral_integral_swap hi]
    _ ≤ (‖a‖ * (perimeter E).toReal) * (volume.restrict (Ioc (0 : ℝ) 1)).real univ := by
      apply norm_integral_le_of_norm_le_const
      exact Filter.Eventually.of_forall fun t => (Real.norm_eq_abs _).trans_le (ht t)
    _ = _ := by simp [Measure.real]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology Convolution

def mollifier (n : ℕ) : ContDiffBump (0 : Cover) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

lemma mollifier_rOut_tendsto : Tendsto (fun n => (mollifier n).rOut) atTop (𝓝 0) := by
  simpa only [mollifier, mul_one, mul_div, mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

def smoothApprox (g : Cover → ℝ) (n : ℕ) : Cover → ℝ :=
  (mollifier n).normed volume ⋆ g

lemma locallyIntegrable_of_bounded {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) : LocallyIntegrable g volume := by
  apply (continuous_const : Continuous (fun _ : Cover => (1 : ℝ))).locallyIntegrable.mono
    hg.aestronglyMeasurable
  exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_one] using hb x

lemma smoothApprox_contDiff {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (smoothApprox g n) :=
  (mollifier n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (mollifier n).contDiff_normed
      (locallyIntegrable_of_bounded hg hb)

lemma smoothApprox_bound {g : Cover → ℝ} (hb : ∀ x, |g x| ≤ 1) (n : ℕ) (x : Cover) :
    |smoothApprox g n x| ≤ 1 := by
  rw [← Real.norm_eq_abs, smoothApprox, convolution_def]
  calc
    _ ≤ ∫ y : Cover, (mollifier n).normed volume y := by
      apply norm_integral_le_of_norm_le (mollifier n).integrable_normed
      exact Eventually.of_forall fun y => by
        rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ((mollifier n).nonneg_normed y), Real.norm_eq_abs]
        exact mul_le_of_le_one_right ((mollifier n).nonneg_normed y) (hb (x - y))
    _ = 1 := (mollifier n).integral_normed

lemma smoothApprox_periodic {g : Cover → ℝ}
    (hp : ∀ n x, g (x + latticeVector n) = g x) (k : ℕ) (n : Fin 3 → ℤ) (x : Cover) :
    smoothApprox g k (x + latticeVector n) = smoothApprox g k x := by
  simp only [smoothApprox, convolution_def, ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [show x + latticeVector n - y = (x - y) + latticeVector n by abel, hp]

lemma smoothApprox_ae_tendsto {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) :
    ∀ᵐ x ∂volume, Tendsto (fun n => smoothApprox g n x) atTop (𝓝 (g x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    mollifier_rOut_tendsto (K := 2) _ (locallyIntegrable_of_bounded hg hb)
  exact Eventually.of_forall fun n => by dsimp [mollifier]; ring_nf; rfl

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

theorem measurable_test_translation_bound {E : Set Torus} (hE : perimeter E ≠ ⊤)
    {g : Cover → ℝ} (hg : Measurable g)
    (hp : ∀ n x, g (x + latticeVector n) = g x)
    (hb : ∀ x, |g x| ≤ 1) (a : Cover) :
    |∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, (g (x + a) - g x)|
      ≤ ‖a‖ * (perimeter E).toReal := by
  have ht := smoothApprox_ae_tendsto hg hb
  have hta := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae ht
  have hlim : ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      Tendsto (fun n => smoothApprox g n (x + a) - smoothApprox g n x)
        atTop (𝓝 (g (x + a) - g x)) := by
    apply ae_restrict_of_ae
    filter_upwards [hta, ht] with x hx hx'
    exact hx.sub hx'
  have him : ∀ n, AEStronglyMeasurable
      (fun x => smoothApprox g n (x + a) - smoothApprox g n x)
        (volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E)) := by
    intro n
    exact (((smoothApprox_contDiff hg hb n).continuous.comp
      (continuous_id.add continuous_const)).sub
        (smoothApprox_contDiff hg hb n).continuous).aestronglyMeasurable
  have hbd : ∀ n, ∀ᵐ x ∂volume.restrict (fundamentalCube ∩ quotientMap ⁻¹' E),
      ‖smoothApprox g n (x + a) - smoothApprox g n x‖ ≤ (2 : ℝ) := by
    intro n
    exact Eventually.of_forall fun x => by
      calc
        _ ≤ ‖smoothApprox g n (x + a)‖ + ‖smoothApprox g n x‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (smoothApprox_bound hb n (x + a)) (smoothApprox_bound hb n x)
        _ = 2 := by norm_num
  have hi := tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
    him (integrable_const 2) hbd hlim
  apply le_of_tendsto hi.abs
  exact Eventually.of_forall fun n => smooth_test_translation_bound hE
    (smoothApprox_contDiff hg hb n) (smoothApprox_periodic hp n) (smoothApprox_bound hb n) a

end CubicTorus

namespace CubicTorus

lemma quotientMap_latticeVector (n : Fin 3 → ℤ) : quotientMap (latticeVector n) = 0 := by
  ext i
  simp [quotientMap, latticeVector]

lemma measurable_characteristic {E : Set Torus} (hE : MeasurableSet E) :
    Measurable (characteristic E) := measurable_const.indicator hE

end CubicTorus
end
end
end

end OAI
