import Mathlib
import OAI.Geometry.SmoothYau.DifferentialEq.ExistsMetricSignQuasimodesSubregions
import OAI.Geometry.SmoothYau.Geometry.BoxProfileIntegralPos
import OAI.Geometry.SmoothYau.Geometry.InverseChartIntrinsicLipschitz
import OAI.Geometry.SmoothYau.Limits.ActualProfileMassPos
import OAI.Geometry.SmoothYau.Limits.CompactExponentialEnvelopeLogBound

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem exists_supported_nodal_quasimodes
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ C > 0,
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
      ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        (∀ y ∈ K, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∀ (J : Type) [Fintype J] (P Cₛ : J → Set (Fin 3 → ℝ)) (ℓ : J → ℝ),
        (∀ a, 0 < ℓ a) → (∀ a, IsOpen (P a)) → (∀ a, Convex ℝ (P a)) →
        (Pairwise fun a b => Disjoint (P a) (P b)) →
        (∀ a, MeasurableSet (Cₛ a)) → (∀ a, IsFiniteMeasure (volume.restrict (Cₛ a))) →
        (∀ a, normalWaveEquiv '' P a ⊆ K) →
        (∀ a, ∀ x ∈ Cₛ a, x ∈ P a ∧
          profileFrequencyScale g φ (normalWaveEquiv x) ≤ ℓ a ∧
          ℓ a ≤ 2*profileFrequencyScale g φ (normalWaveEquiv x) ∧
          ∀ j : Fin 3, x+Pi.single j (ε/(n*ℓ a)) ∈ P a) →
        0 < ∑ a, ℓ a*(volume (Cₛ a)).toReal →
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ O ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*φ x) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y+n*(n+2)*u y) x‖ ≤
              C*(n^(D+1))⁻¹*Real.exp (n*φ x)) ∧
          (∀ y ∈ E, 1/n^110 ≤ ‖realWaveJet n (W y) ((w+u) ∘ normalWaveEquiv) y‖) ∧
          ENNReal.ofReal ((p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal)) <
            SignTests.signCertificate P (fun a => ε/(n*ℓ a)) ((w+u) ∘ normalWaveEquiv) ∧
          ENNReal.ofReal ((p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal)) <
            36*Measure.hausdorffMeasure 2 ((⋃ a, P a) ∩ {x | (w+u) (normalWaveEquiv x)=0}) := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := exists_metric_sign_quasimodes_supported g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,C,hC,N,hN,hdata⟩ := hdata φ hφ hnc hcrit m D T₀ H hT₀ hH
  refine ⟨c₀,hc₀,C,hC,N,hN,?_⟩
  intro n hn S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog hb
    J _ P Cₛ ℓ hℓ hP hPc hPd hCₛ hfin hPK hregion hmass
  have hn0 : 0 < n := zero_lt_one.trans_le (hN.trans hn)
  let d : J → ℝ := fun a => ε/(n*ℓ a)
  let ν : J → Measure NormalWaveSpace := fun a => coordinateRegionMeasure (Cₛ a)
  have hd : ∀ a, 0 < d a := fun a => div_pos hε (mul_pos hn0 (hℓ a))
  have hν : ∀ a, IsFiniteMeasure (ν a) := fun a => coordinateRegionMeasure_finite (Cₛ a)
  have htotal : (∑ a, (d a)⁻¹*(ν a univ).toReal) =
      (n/ε)*(∑ a, ℓ a*(volume (Cₛ a)).toReal) := by
    simp only [ν,coordinateRegionMeasure_univ,d,inv_div]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _; ring
  have hpos : 0 < ∑ a, (d a)⁻¹*(ν a univ).toReal := by
    rw [htotal]; exact mul_pos (div_pos hn0 hε) hmass
  have hreg (a : J) : ∀ᵐ y ∂ν a, y ∈ K ∧ profileFrequencyScale g φ y ≤ ℓ a ∧
      ℓ a ≤ 2*profileFrequencyScale g φ y ∧
      ∀ j, packetAxisShift y n ε (ℓ a) j ∈ K := by
    apply coordinateRegionMeasure_ae (hCₛ a)
    intro x hx
    have hr := hregion a x hx
    refine ⟨hPK a ⟨x,hr.1,rfl⟩,hr.2.1,hr.2.2.1,?_⟩
    intro j
    have hh := hPK a ⟨x+Pi.single j (ε/(n*ℓ a)),hr.2.2.2 j,rfl⟩
    simpa only [normalWaveEquiv_axis_shift,packetAxisShift] using hh
  obtain ⟨u,hu,huc,hus,hder,hjet,hscore⟩ := hdata n hn S hS E hES hEK w hw W hW hW0
    hWlower hWupper hwbound hlog hb J ℓ (fun a => (d a)⁻¹)
    (fun a => (inv_pos.mpr (hd a)).le) ν hν hpos hreg
  have hcore (a : J) (x) (hx : x ∈ Cₛ a) (j : Fin 3) :
      x ∈ P a ∧ x+Pi.single j (d a) ∈ P a :=
    ⟨(hregion a x hx).1,(hregion a x hx).2.2.2 j⟩
  have hsc := coordinate_region_score_le_certificate P Cₛ d hd hcore hν (hw.continuous.add hu.continuous)
  have hnod := coordinate_region_score_le_nodal P Cₛ d hd hP hPc hPd hcore hν (hw.continuous.add hu.continuous)
  have he : (p₀/2)*(∑ a, (d a)⁻¹*(ν a univ).toReal) =
      (p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal) := by rw [htotal]; ring
  rw [he] at hscore
  have hlt := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity :
    0 ≤ (p₀/(2*ε))*n*(∑ a, ℓ a*(volume (Cₛ a)).toReal))).mpr hscore
  exact ⟨u,hu,huc,hus,hder,hjet,hlt.trans_le hsc,hlt.trans_le hnod⟩

end

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
open BoxIntegral

theorem exists_supported_box_nodal_quasimodes
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I ⊆ K →
    ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
    (∀ J ∈ partition, 0 < ℓ J) ∧
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ C > 0,
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
      ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        (∀ y ∈ K, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ O ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*φ x) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y+n*(n+2)*u y) x‖ ≤
              C*(n^(D+1))⁻¹*Real.exp (n*φ x)) ∧
          (∀ y ∈ E, 1/n^110 ≤ ‖realWaveJet n (W y) ((w+u) ∘ normalWaveEquiv) y‖) ∧
          ENNReal.ofReal ((p₀/(16*ε))*n*(∫ x in Box.Icc I, profileFrequencyScale g φ (normalWaveEquiv x))) <
            SignTests.signCertificate
              (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
              (fun a => ε/(n*ℓ a.val)) ((w+u) ∘ normalWaveEquiv) ∧
          ENNReal.ofReal ((p₀/(16*ε))*n*(∫ x in Box.Icc I, profileFrequencyScale g φ (normalWaveEquiv x))) <
            36*Measure.hausdorffMeasure 2 ((⋃ a : {J : Box (Fin 3) // J ∈ partition.boxes}, Box.Ioo a.val) ∩ {x | (w+u) (normalWaveEquiv x)=0}) := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := exists_supported_nodal_quasimodes g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit I hIK
  let L : (Fin 3 → ℝ) → ℝ := fun x => profileFrequencyScale g φ (normalWaveEquiv x)
  have hL : Continuous L := Real.continuous_sqrt.comp
    ((continuous_profileFrequencyEnergy g hφ).comp normalWaveEquiv.continuous)
  have hL1 : ∀ x, 1 ≤ L x := fun x => profileFrequencyScale_ge_one g φ _
  obtain ⟨partition,hπ,ℓ,hℓ⟩ := exists_profile_box_partition I L hL.continuousOn
    (fun x _ => zero_lt_one.trans_le (hL1 x))
  let J := {J : Box (Fin 3) // J ∈ partition.boxes}
  let P : J → Set (Fin 3 → ℝ) := fun a => Box.Ioo a.val
  let Cₛ : J → Set (Fin 3 → ℝ) := fun a => Box.Icc (middleBox a.val)
  have hmass := middleBox_partition_mass I L hL.continuousOn partition hπ ℓ
    (fun a ha x hx => (hℓ a ha).2 x hx |>.2)
  have hmasspos : 0 < ∑ a : J, ℓ a.val*(volume (Cₛ a)).toReal := by
    exact (div_pos (box_profile_integral_pos I L hL.continuousOn (fun x _ => hL1 x)) (by norm_num)).trans_le hmass
  have hshifts : ∀ᶠ n : ℝ in atTop, ∀ a : J, ∀ x ∈ Cₛ a, ∀ j : Fin 3,
      x+Pi.single j (ε/(n*ℓ a.val)) ∈ P a := by
    rw [Filter.eventually_all]
    intro a
    exact middleBox_eventually_shift_mem a.val hε (hℓ a.val a.property).1
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.1 hshifts
  refine ⟨partition,hπ,ℓ,fun a ha => (hℓ a ha).1,?_⟩
  intro m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,C,hC,N,hN,hdata⟩ := hdata φ hφ hnc hcrit m D T₀ H hT₀ hH
  refine ⟨c₀,hc₀,C,hC,max N N₁,hN.trans (le_max_left _ _),?_⟩
  intro n hn S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog hb
  have hn0 : 0 < n := zero_lt_one.trans_le (hN.trans ((le_max_left _ _).trans hn))
  have hPK (a : J) : normalWaveEquiv '' P a ⊆ K := by
    rintro y ⟨x,hx,rfl⟩
    exact hIK ⟨x,Box.le_iff_Icc.mp (partition.le_of_mem a.property) (Box.Ioo_subset_Icc a.val hx),rfl⟩
  have hregion (a : J) (x : Fin 3 → ℝ) (hx : x ∈ Cₛ a) :
      x ∈ P a ∧ profileFrequencyScale g φ (normalWaveEquiv x) ≤ ℓ a.val ∧
      ℓ a.val ≤ 2*profileFrequencyScale g φ (normalWaveEquiv x) ∧
      ∀ j : Fin 3, x+Pi.single j (ε/(n*ℓ a.val)) ∈ P a := by
    have hxp := middleBox_Icc_subset a.val hx
    have hscale := (hℓ a.val a.property).2 x (Box.Ioo_subset_Icc a.val hxp)
    refine ⟨hxp,hscale.2,?_,hN₁ n ((le_max_right _ _).trans hn) a x hx⟩
    change ℓ a.val ≤ 2*L x
    linarith [hscale.1]
  obtain ⟨u,hu,huc,hus,hder,hjet,hscore,hnod⟩ :=
    hdata n ((le_max_left _ _).trans hn) S hS E hES hEK w hw W hW hW0
      hWlower hWupper hwbound hlog hb J P Cₛ (fun a => ℓ a.val)
      (fun a => (hℓ a.val a.property).1) (fun a => box_Ioo_open a.val)
      (fun a => box_Ioo_convex a.val) (partition_Ioo_disjoint I partition)
      (fun a => (middleBox a.val).measurableSet_Icc)
      (fun a => isFiniteMeasure_restrict.mpr ((middleBox a.val).measure_Icc_lt_top volume).ne)
      hPK hregion hmasspos
  have hle : (p₀/(16*ε))*n*(∫ x in Box.Icc I, L x) ≤
      (p₀/(2*ε))*n*(∑ a : J, ℓ a.val*(volume (Cₛ a)).toReal) := by
    calc
      _ = (p₀/(2*ε))*n*((∫ x in Box.Icc I, L x)/8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  exact ⟨u,hu,huc,hus,hder,hjet,(ENNReal.ofReal_le_ofReal hle).trans_lt hscore,
    (ENNReal.ofReal_le_ofReal hle).trans_lt hnod⟩

end

section
open Set Filter MeasureTheory BoxIntegral
open scoped Topology ContDiff

def normalCoordinateVolume : Measure NormalWaveSpace := Measure.map normalWaveEquiv volume

instance normalCoordinateVolume_finiteOnCompacts : IsFiniteMeasureOnCompacts normalCoordinateVolume where
  lt_top_of_isCompact K hK := by
    rw [normalCoordinateVolume,Measure.map_apply normalWaveEquiv.continuous.measurable hK.measurableSet]
    have he : normalWaveEquiv ⁻¹' K = normalWaveEquiv.symm '' K := by
      ext x
      constructor
      · intro hx; exact ⟨normalWaveEquiv x,hx,normalWaveEquiv.symm_apply_apply x⟩
      · rintro ⟨y,hy,h⟩
        change normalWaveEquiv x ∈ K
        rw [←h,normalWaveEquiv.apply_symm_apply]
        exact hy
    rw [he]
    exact (hK.image normalWaveEquiv.symm.continuous).measure_lt_top

lemma box_Ioo_closure (I : Box (Fin 3)) : closure (Box.Ioo I) = Box.Icc I := by
  rw [Box.Icc_def,←Set.pi_univ_Icc]
  change closure (Set.pi univ (fun i => Set.Ioo (I.lower i) (I.upper i))) =
    Set.pi univ (fun i => Set.Icc (I.lower i) (I.upper i))
  rw [closure_pi_set]
  congr 1
  funext i
  exact closure_Ioo (I.lower_lt_upper i).ne

lemma normal_box_closure (I : Box (Fin 3)) :
    closure (normalWaveEquiv '' Box.Ioo I) = normalWaveEquiv '' Box.Icc I := by
  have he := normalWaveEquiv.toHomeomorph.image_closure (Box.Ioo I)
  change normalWaveEquiv '' closure (Box.Ioo I) = closure (normalWaveEquiv '' Box.Ioo I) at he
  rw [←he,box_Ioo_closure]

lemma normal_box_open (I : Box (Fin 3)) : IsOpen (normalWaveEquiv '' Box.Ioo I) :=
  normalWaveEquiv.toHomeomorph.isOpenMap _ (isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo))

lemma normal_box_measure_ne_zero (I : Box (Fin 3)) :
    normalCoordinateVolume (normalWaveEquiv '' Box.Ioo I) ≠ 0 := by
  rw [normalCoordinateVolume,Measure.map_apply normalWaveEquiv.continuous.measurable
    (normal_box_open I).measurableSet,Set.preimage_image_eq _ normalWaveEquiv.injective]
  have hv : 0 < (volume (Box.Ioo I)).toReal := by
    rw [measure_congr I.Ioo_ae_eq_Icc,←measure_congr I.coe_ae_eq_Icc,Box.volume_apply']
    exact Finset.prod_pos (fun i _ => sub_pos.mpr (I.lower_lt_upper i))
  intro h
  rw [h,ENNReal.toReal_zero] at hv
  exact lt_irrefl _ hv

lemma profileSpeed_le_frequencyScale (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) :
    actualProfileSpeed g φ x ≤ profileFrequencyScale g φ x := by
  apply Real.sqrt_le_sqrt
  change selfMetricFlat g x (coordinateMetricGradient g φ x) (coordinateMetricGradient g φ x) ≤
    1+selfMetricFlat g x (coordinateMetricGradient g φ x) (coordinateMetricGradient g φ x)
  linarith

lemma actual_profile_mass_le_box_frequency_integral
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) {φ : NormalWaveSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (I : Box (Fin 3)) :
    actualProfileMass g φ normalCoordinateVolume (normalWaveEquiv '' Box.Ioo I) ≤
      ∫ x in Box.Icc I, profileFrequencyScale g φ (normalWaveEquiv x) := by
  have he := normalWaveEquiv.toHomeomorph.measurableEmbedding.setIntegral_map
    (μ := volume) (actualProfileSpeed g φ) (normalWaveEquiv '' Box.Ioo I)
  change (∫ x in normalWaveEquiv '' Box.Ioo I, actualProfileSpeed g φ x ∂Measure.map normalWaveEquiv volume) =
    (∫ x in normalWaveEquiv ⁻¹' (normalWaveEquiv '' Box.Ioo I), actualProfileSpeed g φ (normalWaveEquiv x)) at he
  rw [actualProfileMass,normalCoordinateVolume,he,Set.preimage_image_eq _ normalWaveEquiv.injective]
  rw [setIntegral_congr_set I.Ioo_ae_eq_Icc]
  apply setIntegral_mono_on
    (((continuous_actualProfileSpeed g hφ).comp normalWaveEquiv.continuous).continuousOn.integrableOn_compact I.isCompact_Icc)
    ((Real.continuous_sqrt.comp ((continuous_profileFrequencyEnergy g hφ).comp normalWaveEquiv.continuous)).continuousOn.integrableOn_compact I.isCompact_Icc)
    I.measurableSet_Icc
  exact fun x _ => profileSpeed_le_frequencyScale g φ _

theorem exists_box_amplified_profile (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (I : Box (Fin 3)) {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (ha : ∀ x ∈ normalWaveEquiv '' Box.Icc I, coordinateMetricGradient g φ x ≠ 0)
    (hstrict : ∀ x ∈ normalWaveEquiv '' Box.Icc I, actualProfileStrict g φ x)
    (T : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ψ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ ψ ∧
      HasCompactSupport (fun x => ψ x-φ x) ∧
      tsupport (fun x => ψ x-φ x) ⊆ normalWaveEquiv '' Box.Ioo I ∧
      (∀ x, |ψ x-φ x| < η) ∧
      (∀ x ∈ normalWaveEquiv '' Box.Icc I,
        coordinateMetricGradient g ψ x ≠ 0 ∧ actualProfileStrict g ψ x) ∧
      T < ∫ x in Box.Icc I, profileFrequencyScale g ψ (normalWaveEquiv x) := by
  have hd : Module.finrank ℝ NormalWaveSpace = 3 := by simp [NormalWaveSpace]
  have hc : IsCompact (closure (normalWaveEquiv '' Box.Ioo I)) := by
    rw [normal_box_closure]
    exact I.isCompact_Icc.image normalWaveEquiv.continuous
  obtain ⟨ψ,hψ,hψc,hψs,hψ0,hψp,hψmass⟩ := actual_metric_profile_amplification hd g hφ
    (normal_box_open I) hc (fun x hx => ha x (by simpa only [normal_box_closure] using hx))
    (fun x hx => hstrict x (by simpa only [normal_box_closure] using hx))
    normalCoordinateVolume (normal_box_measure_ne_zero I) T hη
  refine ⟨ψ,hψ,hψc,hψs,hψ0,?_,hψmass.trans_le (actual_profile_mass_le_box_frequency_integral g hψ I)⟩
  intro x hx
  exact hψp x (by simpa only [normal_box_closure] using hx)

end



section
open Set Filter Function Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [EMetricSpace N] [MeasurableSpace N] [BorelSpace N]

theorem regular_level_local_finite {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 1 f x) (hd : fderiv ℝ f x ≠ 0)
    {φ : E → N} {B : Set E} (hB : B ∈ 𝓝 x) {C : ℝ≥0}
    (hφ : LipschitzOnWith C φ B) :
    ∃ O ∈ 𝓝 x, Measure.hausdorffMeasure (Module.finrank ℝ E - 1 : ℕ)
      (φ '' {y | y ∈ O ∧ f y = f x}) < (∞ : ℝ≥0∞) := by
  let L := fderiv ℝ f x
  have hL : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    apply surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (f := L.toLinearMap) (by simp)
    intro hh
    apply hd
    ext y
    exact DFunLike.congr_fun hh y
  have hs : HasStrictFDerivAt f L x := hf.hasStrictFDerivAt one_ne_zero
  let e := hs.implicitToOpenPartialHomeomorph f L hL
  let g := hs.implicitFunction f L hL (f x)
  have hdx : HasStrictFDerivAt g L.ker.subtypeL 0 := hs.to_implicitFunction hL
  have hg0 : g 0 = x := hs.implicitFunction_apply_image hL
  obtain ⟨K,V,hV,hgV⟩ := hdx.exists_lipschitzOnWith
  have hN : V ∩ g ⁻¹' B ∈ 𝓝 (0 : L.ker) :=
    inter_mem hV (hdx.continuousAt.tendsto (hg0 ▸ hB))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hN
  let S := ball (0 : L.ker) r
  have hSg : MapsTo g S B := fun y hy => (hrsub hy).2
  have hgS : LipschitzOnWith K g S := hgV.mono (fun y hy => (hrsub hy).1)
  have he : x ∈ e.source := hs.mem_implicitToOpenPartialHomeomorph_source hL
  have he0 : e x = (f x,0) := hs.implicitToOpenPartialHomeomorph_self hL
  have hpre : e ⁻¹' (Set.univ ×ˢ S) ∈ 𝓝 x := by
    apply (e.continuousAt he).tendsto
    rw [he0]
    exact IsOpen.mem_nhds (isOpen_univ.prod isOpen_ball) ⟨mem_univ _,mem_ball_self hr⟩
  let O := e.source ∩ e ⁻¹' (Set.univ ×ˢ S)
  have hO : O ∈ 𝓝 x := inter_mem (e.open_source.mem_nhds he) hpre
  refine ⟨O,hO,?_⟩
  have hsub : φ '' {y | y ∈ O ∧ f y = f x} ⊆ (φ ∘ g) '' S := by
    rintro _ ⟨y,hy,rfl⟩
    refine ⟨(e y).2,hy.1.2.2,?_⟩
    change φ (g (e y).2) = φ y
    congr 1
    change e.symm (f x,(e y).2) = y
    rw [← hy.2]
    change e.symm (e y) = y
    exact e.left_inv hy.1.1
  have hdim : Module.finrank ℝ L.ker = Module.finrank ℝ E - 1 := by
    have hh := LinearMap.finrank_range_add_finrank_ker L.toLinearMap
    rw [hL] at hh
    simp only [finrank_top, Module.finrank_self] at hh
    omega
  let : MeasurableSpace L.ker := borel L.ker
  let : BorelSpace L.ker := ⟨rfl⟩
  have hfinite : Measure.hausdorffMeasure (Module.finrank ℝ E - 1 : ℕ) S < (∞ : ℝ≥0∞) := by
    rw [← hdim]
    exact lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : L.ker) r).measure_lt_top
  apply lt_of_le_of_lt (measure_mono hsub)
  apply lt_of_le_of_lt ((hφ.comp hgS hSg).hausdorffMeasure_image_le (by positivity))
  rw [ENNReal.rpow_natCast]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hfinite

end



section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

lemma compact_coordinate_regular_level_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) {K : Set E} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, f x = 0 → fderiv ℝ f x ≠ 0) :
    Measure.hausdorffMeasure (Module.finrank ℝ E-1 : ℕ) (K ∩ {x | f x=0}) < (∞ : ℝ≥0∞) := by
  let Z := K ∩ {x | f x=0}
  have hZ : IsCompact Z := hK.inter_right (isClosed_eq hf.continuous continuous_const)
  apply hZ.measure_lt_top_of_nhdsWithin
  intro x hx
  obtain ⟨O,hO,hfin⟩ := regular_level_local_finite hf.contDiffAt (hreg x hx.1 hx.2)
    (B:=univ) (φ:=id) (C:=1) univ_mem (LipschitzWith.id.lipschitzOnWith)
  refine ⟨O ∩ Z, by simpa only [inter_comm] using inter_mem_nhdsWithin Z hO,?_⟩
  apply lt_of_le_of_lt (measure_mono ?_) hfin
  intro y hy
  exact ⟨y,⟨hy.1,hy.2.2.trans hx.2.symm⟩,rfl⟩

lemma realWaveJet_pos_regular {f : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ} {n W : ℝ}
    (hp : 0 < ‖realWaveJet n W f x‖) (hf : f x=0) : fderiv ℝ f x ≠ 0 := by
  intro hd
  have he : realWaveJet n W f x=0 := by
    ext i
    rcases i with i|i <;> simp [realWaveJet,hd,hf]
  rw [he,norm_zero] at hp
  exact lt_irrefl _ hp

lemma noncancelling_coordinate_nodal_finite
    {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : Set (Fin 3 → ℝ)}
    (hK : IsCompact K) {n : ℝ} (hn : 0 < n) (W : (Fin 3 → ℝ) → ℝ)
    (hjet : ∀ y ∈ K, 1/n^110 ≤ ‖realWaveJet n (W y) f y‖) :
    Measure.hausdorffMeasure 2 (K ∩ {x | f x=0}) < (∞ : ℝ≥0∞) := by
  have hr : ∀ x ∈ K, f x=0 → fderiv ℝ f x ≠ 0 := by
    intro x hx hz
    exact realWaveJet_pos_regular ((by positivity : 0 < 1/n^110).trans_le (hjet x hx)) hz
  simpa using compact_coordinate_regular_level_finite hf hK hr

end



section
open Set Filter MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal

theorem exists_arbitrarily_large_nodal_quasimodes
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) (I : Box (Fin 3))
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hIO : normalWaveEquiv '' Box.Icc I ⊆ O)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (ha : ∀ x ∈ normalWaveEquiv '' Box.Icc I, coordinateMetricGradient g φ x ≠ 0)
    (hstrict : ∀ x ∈ normalWaveEquiv '' Box.Icc I, actualProfileStrict g φ x)
    {A η : ℝ} (hA : 0 < A) (hη : 0 < η) :
    ∃ ψ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ ψ ∧
      HasCompactSupport (fun x => ψ x-φ x) ∧
      tsupport (fun x => ψ x-φ x) ⊆ normalWaveEquiv '' Box.Ioo I ∧
      (∀ x, |ψ x-φ x| < η) ∧
      (∀ x ∈ normalWaveEquiv '' Box.Icc I,
        coordinateMetricGradient g ψ x ≠ 0 ∧ actualProfileStrict g ψ x) ∧
      ∀ m D : ℕ, ∃ C > 0, ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n →
        ∃ u : NormalWaveSpace → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ O ∧
          (∀ x : NormalWaveSpace, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j u x‖ ≤ C*n^(j+4)*Real.exp (n*ψ x) ∧
            ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami g u y+n*(n+2)*u y) x‖ ≤
              C*(n^(D+1))⁻¹*Real.exp (n*ψ x)) ∧
          (∀ y ∈ Box.Icc I, 1/n^110 ≤
            ‖realWaveJet n (Real.exp (n*ψ (normalWaveEquiv y))) (u ∘ normalWaveEquiv) y‖) ∧
          Measure.hausdorffMeasure 2 (Box.Icc I ∩ {x | u (normalWaveEquiv x)=0}) < (∞:ℝ≥0∞) ∧
          ENNReal.ofReal (A*n) <
            Measure.hausdorffMeasure 2 (Box.Icc I ∩ {x | u (normalWaveEquiv x)=0}) := by
  classical
  let K := normalWaveEquiv '' Box.Icc I
  have hK : IsCompact K := I.isCompact_Icc.image normalWaveEquiv.continuous
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := exists_supported_box_nodal_quasimodes g hK hO hIO
  obtain ⟨ψ,hψ,hψc,hψs,hψ0,hψp,hψmass⟩ := exists_box_amplified_profile g I hφ ha hstrict
    ((576*ε/p₀)*A) hη
  refine ⟨ψ,hψ,hψc,hψs,hψ0,hψp,?_⟩
  have hncrit (x : NormalWaveSpace) (hx : x ∈ K) : fderiv ℝ ψ x ≠ 0 := by
    intro hf
    apply (hψp x hx).1
    simp [coordinateMetricGradient,hf]
  obtain ⟨partition,hπ,ℓ,hℓ,hdata⟩ := hdata ψ hψ (fun x hx _ => (hψp x hx).2)
    (fun x hx hf => (hncrit x hx hf).elim) I (Subset.rfl)
  have hψc' : ContDiff ℝ ∞ (ψ ∘ normalWaveEquiv) := hψ.comp normalWaveEquiv.contDiff
  obtain ⟨H,hH,hlog⟩ := compact_exponential_envelope_log_bound I.isCompact_Icc hψc'
  intro m D
  obtain ⟨c₀,hc₀,C,hC,N,hN,hdata⟩ := hdata m D 0 H le_rfl hH
  refine ⟨C,hC,N,hN,?_⟩
  intro n hn
  have hn0 : 0 < n := zero_lt_one.trans_le (hN.trans hn)
  let W : (Fin 3 → ℝ) → ℝ := fun y => Real.exp (n*ψ (normalWaveEquiv y))
  have hW : Differentiable ℝ W := (hψc'.differentiable (by simp)).const_mul n |>.exp
  have hWupper (y : Fin 3 → ℝ) (hy : y ∈ Box.Icc I) :
      W y ≤ (1+n^6)*Real.exp (n*ψ (normalWaveEquiv y)) := by
    dsimp only [W]
    nlinarith [Real.exp_pos (n*ψ (normalWaveEquiv y)),pow_nonneg hn0.le 6]
  have hEK : Box.Icc I ⊆ normalWaveEquiv.symm '' K := by
    intro x hx
    exact ⟨normalWaveEquiv x,⟨x,hx,rfl⟩,normalWaveEquiv.symm_apply_apply x⟩
  have hzero (y : Fin 3 → ℝ) (hy : y ∈ Box.Icc I) (j : ℕ) (hj : j ≤ 2) :
      ‖iteratedFDeriv ℝ j ((fun _ : NormalWaveSpace => (0:ℝ)) ∘ normalWaveEquiv) y‖ ≤
        0*n^j*W y := by simp [Function.comp_def]
  obtain ⟨u,hu,huc,hus,hder,hjet,hscore,hnod⟩ := hdata n hn (Box.Icc I)
    (by simpa only [Box.Icc_def] using convex_Icc I.lower I.upper)
    (Box.Icc I) Subset.rfl hEK (fun _ => 0) contDiff_const W hW
    (fun _ => Real.exp_pos _) (fun _ _ => le_rfl) hWupper hzero
    (fun y hy => hlog n hn0.le y hy)
    (fun y _ => by simpa using (mul_pos hc₀ (Real.exp_pos (n*ψ y))).le)
  have hmass : 36*(A*n) < (p₀/(16*ε))*n*
      (∫ x in Box.Icc I, profileFrequencyScale g ψ (normalWaveEquiv x)) := by
    have h := mul_lt_mul_of_pos_left hψmass (show 0 < (p₀/(16*ε))*n by positivity)
    have he : (p₀/(16*ε))*n*((576*ε/p₀)*A)=36*(A*n) := by
      field_simp
      ring
    rwa [he] at h
  have hinc : (⋃ a : {J : Box (Fin 3) // J ∈ partition.boxes}, Box.Ioo a.val) ⊆ Box.Icc I := by
    intro x hx
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
    exact Box.le_iff_Icc.mp (partition.le_of_mem a.property) (Box.Ioo_subset_Icc _ ha)
  have hnod' : ENNReal.ofReal (36*(A*n)) < 36*Measure.hausdorffMeasure 2
      (Box.Icc I ∩ {x | u (normalWaveEquiv x)=0}) := by
    exact (ENNReal.ofReal_le_ofReal hmass.le).trans_lt
      (hnod.trans_le (mul_le_mul_right (measure_mono (by
        intro x hx
        exact ⟨hinc hx.1,by simpa only [Pi.zero_apply,Pi.add_apply,zero_add] using hx.2⟩)) _))
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 36)] at hnod'
  norm_num only [ENNReal.ofReal_ofNat] at hnod'
  have hjet' : ∀ y ∈ Box.Icc I, 1/n^110 ≤
      ‖realWaveJet n (W y) (u ∘ normalWaveEquiv) y‖ := by
    simpa only [show (fun _ : NormalWaveSpace => (0 : ℝ)) = 0 from rfl, zero_add] using hjet
  refine ⟨u,hu,huc,hus,hder,hjet',?_,?_⟩
  · exact noncancelling_coordinate_nodal_finite
      ((hu.comp normalWaveEquiv.contDiff).of_le (by simp)) I.isCompact_Icc hn0 W hjet'
  · exact (ENNReal.mul_lt_mul_iff_right (by norm_num : (36:ℝ≥0∞) ≠ 0) (by norm_num)).mp hnod'

end


open Set Filter Metric Manifold MeasureTheory Bundle
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Function Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [EMetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] [MeasurableSpace M] [BorelSpace M]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

theorem compact_regular_level_intrinsic_finite {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) {K : Set M} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, u x = 0 →
      fderiv ℝ (u ∘ (chartAt E x).symm) (chartAt E x x) ≠ 0) :
    Measure.hausdorffMeasure (Module.finrank ℝ E - 1 : ℕ) (K ∩ {x | u x = 0}) < (∞ : ℝ≥0∞) := by
  let Z := K ∩ {x | u x = 0}
  have hZ : IsCompact Z := hK.inter_right (isClosed_eq hu.continuous continuous_const)
  apply hZ.measure_lt_top_of_nhdsWithin
  intro x hx
  let c := chartAt E x
  have hxs : x ∈ c.source := mem_chart_source E x
  have hxt : c x ∈ c.target := c.map_source hxs
  have hcU : ContDiffAt ℝ 1 (u ∘ c.symm) (c x) := by
    apply (contMDiffAt_iff_contDiffAt.mp ((hu (c.symm (c x))).comp (c x)
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hxt))).of_le
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 1
  obtain ⟨r,hr,C,_,_,hCL⟩ := inverse_chart_intrinsic_lipschitz (E := E) x
  have hCL' : LipschitzOnWith C c.symm (ball (c x) r) := by
    intro y hy z hz
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ,E))]
    exact hCL y hy z hz
  obtain ⟨O,hO,hfin⟩ := regular_level_local_finite hcU (hreg x hx.1 hx.2)
    (ball_mem_nhds (c x) hr) hCL'
  let V := c.source ∩ c ⁻¹' O
  have hV : V ∈ 𝓝 x := inter_mem (c.open_source.mem_nhds hxs) ((c.continuousAt hxs).tendsto hO)
  refine ⟨V ∩ Z, by simpa only [inter_comm] using inter_mem_nhdsWithin Z hV, ?_⟩
  apply lt_of_le_of_lt (measure_mono ?_) hfin
  intro y hy
  refine ⟨c y,⟨hy.1.2,?_⟩,c.left_inv hy.1.1⟩
  simp only [Function.comp_apply, c.left_inv hy.1.1, c.left_inv hxs]
  exact hy.2.2.trans hx.2.symm


end YauCounterexamples
end

end OAI
