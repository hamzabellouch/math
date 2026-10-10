import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.DensitySecondMoment
import OAI.Analysis.VlasovMaxwell.Retarded.ConeEulerianIntegrand

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma physicalBinBase_prefix {α : Phase → ℝ → Phase} {T : ℝ} (zX : Phase)
    (C : ClosedConeBin) {J : Set ℝ} (hJ : J⊆Icc 0 T) :
    physicalBinBase (fun t => (prefixFlow α T zX t).2) C J =
      physicalBinBase (fun t => (α zX t).2) C J := by
  ext z
  by_cases hz : z.1∈J
  · simp only [physicalBinBase,mem_ofPred_eq,prefixFlow,prefixClamp_eq (hJ hz)]
  · simp only [physicalBinBase,mem_ofPred_eq,hz,false_and]

lemma PhaseFlowOn.physicalBin_weighted_occupation {s : Solution} {T a b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (C : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hS0 : tsupport (fun z => s.f (0,z))⊆S)
    (hJ : Icc a b⊆Icc 0 T) (hR : 0≤C.rmin) (hD : 0≤C.Dmin) :
    ENNReal.ofReal (C.rmin^2*C.Dmin) *
      (∫⁻ z : ConeCoordinate,physicalBinDensity s (fun t => (F.flow zX t).1)
        (fun t => (F.flow zX t).2) C z.1 z.2.1 z.2.2
        ∂physicalBinMeasure (fun t => (F.flow zX t).2) C (Icc a b)) ≤
      coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T C S a b (max 0 (a-C.rmax)) (min T (b-C.rmin))) := by
  let c := max 0 (a-C.rmax)
  let d := min T (b-C.rmin)
  let H := closedBinEulerian F.flow zX T C S a b c d
  let X : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).1
  let V : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).2
  let g : ConeCoordinate → ℝ≥0∞ := fun z =>
    physicalBinDensity {s with f := prefixParticle s T} X V C z.1 z.2.1 z.2.2
  have hC : Icc c d⊆Icc 0 T := fun _ hr =>
    ⟨(le_max_left _ _).trans hr.1,hr.2.trans (min_le_left _ _)⟩
  have hH : MeasurableSet H := F.measurable_closedBinEulerian hs hT zX C hS hJ hC
  have hα : Continuous (fun t => prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hX : Measurable X := hα.fst.measurable
  have hV : Measurable V := hα.snd.measurable
  have hg : Measurable g := measurable_coneBinDensity
    (hs.continuous_prefixParticle hT).measurable hX hV C
  have hμ : physicalBinMeasure (fun t => (F.flow zX t).2) C (Icc a b) =
      physicalBinMeasure V C (Icc a b) := by
    unfold physicalBinMeasure V
    rw [physicalBinBase_prefix zX C hJ]
  have hgactual (t r : ℝ) (n : Sphere) (ht : t∈Icc 0 T) (hr : r∈Icc 0 T) :
      g (t,r,n)=physicalBinDensity s (fun t => (F.flow zX t).1)
        (fun t => (F.flow zX t).2) C t r n := by
    simp only [g,physicalBinDensity,X,V,prefixFlow,prefixClamp_eq ht,
      prefixParticle,prefixClamp_eq hr]
  rw [hμ]
  have he : (∫⁻ z : ConeCoordinate,physicalBinDensity s (fun t => (F.flow zX t).1)
        (fun t => (F.flow zX t).2) C z.1 z.2.1 z.2.2 ∂physicalBinMeasure V C (Icc a b)) =
      ∫⁻ z,g z ∂physicalBinMeasure V C (Icc a b) := by
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV C measurableSet_Icc)
    intro z hz
    exact (hgactual z.1 z.2.1 z.2.2 (hJ hz.1)
      ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩).symm
  rw [he,physicalBin_integral_eq_triangle hV C measurableSet_Icc hJ hg,
    F.cone_occupation_eq_receiver_coordinates hs hT zX hH]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro t ht
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro r hr
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro n
  dsimp only
  have ht' := Ioo_subset_Icc_self ht
  have hr' : r∈Ioo 0 T := ⟨hr.1,hr.2.trans ht.2⟩
  by_cases hz : (t,r,n)∈physicalBinBase V C (Icc a b)
  · rw [indicator_of_mem hz,hgactual t r n ht' (Ioo_subset_Icc_self hr')]
    have hz' : (t,r,n)∈physicalBinBase (fun t => (F.flow zX t).2) C (Icc a b) := by
      rwa [show V=(fun t => (prefixFlow F.flow T zX t).2) from rfl,
        physicalBinBase_prefix zX C hJ] at hz
    have hrC : r∈Icc c d := by
      constructor
      · exact max_le hr.1.le (by linarith [hz'.1.1,hz'.2.2.1.2])
      · exact le_min hr'.2.le (by linarith [hz'.1.2,hz'.2.2.1.1])
    have hden := F.physicalBinDensity_le_Eulerian hs zX C hS0 n hJ hC hr' hrC hr.2 ht.2 hz'
    have hw : C.rmin^2*C.Dmin ≤ (t-r)^2*(1-dot n.1 (velocity (F.flow zX t).2)) := by
      exact mul_le_mul (sq_le_sq₀ hR (sub_pos.mpr hr.2).le |>.mpr hz'.2.2.1.1)
        hz'.2.2.2.2.1 hD (sq_nonneg _)
    change _ ≤ coneEulerianIntegrand s T X V H (t,r,n)
    have hprefix : coneEulerianIntegrand s T X V H (t,r,n) =
        ENNReal.ofReal ((t-r)^2*(1-dot n.1 (velocity (F.flow zX t).2))) *
          ∫⁻ v : Vec,H.indicator (fun p => ENNReal.ofReal (s.f p))
            (r,((F.flow zX t).1-(t-r) • n.1,v)) := by
      simp only [coneEulerianIntegrand,X,V,prefixFlow,prefixClamp_eq ht']
      congr 1
      apply lintegral_congr
      intro v
      by_cases hp : (r,((F.flow zX t).1-(t-r) • n.1,v))∈H
      · simp only [indicator_of_mem hp,prefixParticle,prefixClamp_eq (Ioo_subset_Icc_self hr')]
      · simp only [indicator_of_notMem hp]
    rw [hprefix]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hw) hden
  · rw [indicator_of_notMem hz,mul_zero]
    exact bot_le

lemma PhaseFlowOn.actual_bin_Cauchy {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) :
    ∃ C₀ : ℝ, 0≤C₀ ∧ ∀ (zX : Phase) (C : ClosedConeBin) (S : Set Phase)
      (a b I P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
      tsupport (fun z => s.f (0,z))⊆S → Icc a b⊆Icc 0 T →
      0<I → 0<P → 0≤θ → 0≤φ → 0≤σ → 0<C.rmin → 0<C.Dmin →
      C.qmax≤P → C.dmax≤8*θ^2 → C.Dmax≤8*φ^2 → C.emax≤8*σ^2 →
      (∀ D∈Icc C.Dmin C.Dmax, DyadicWindow k j (Real.sqrt (D/2))) →
      let X : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).1
      let V : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).2
      let N : ConeCoordinate → ℝ≥0∞ := fun z => physicalBinDensity s X V C z.1 z.2.1 z.2.2
      let D := ENNReal.ofReal (128*C₀*P^3*(min θ σ)^2)
      let M := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T C S a b (max 0 (a-C.rmax)) (min T (b-C.rmin))) /
          ENNReal.ofReal (C.rmin^2*C.Dmin)
      (∫⁻ z : ConeCoordinate, ENNReal.ofReal (z.1-z.2.1) *
        ENNReal.ofReal (prefixConeGood s T X z) * N z ∂physicalBinMeasure V C (Icc a b)) ≤
      (ENNReal.ofReal I * goodFieldBudget s X (fun t => velocity (V t)) k a b I j)^(1/2:ℝ) *
        (min (D^2*(volume (Icc a b)*ENNReal.ofReal (C.rmax-C.rmin)*ENNReal.ofReal (384*φ^2)))
          (D*M))^(1/2:ℝ) := by
  obtain ⟨C₀,hC₀,hbound⟩ := F.physicalBinDensity_bounds hs hT
  refine ⟨C₀,hC₀,?_⟩
  intro zX C S a b I P θ φ σ k j hS hS0 hJ hI hP hθ hφ hσ hR hD hq hd hDmax he hangle
  dsimp only
  let X : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).1
  let V : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).2
  let N : ConeCoordinate → ℝ≥0∞ := fun z => physicalBinDensity s X V C z.1 z.2.1 z.2.2
  let μ := physicalBinMeasure V C (Icc a b)
  have hα : Continuous (fun t => prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hX : Measurable X := hα.fst.measurable
  have hV : Measurable V := hα.snd.measurable
  have hN : AEMeasurable N μ :=
    physicalBinDensity_aemeasurable hs hT hX hV C measurableSet_Icc hJ
  have hG := hs.measurable_prefixConeGood hT hX
  have hW : AEMeasurable (fun z : ConeCoordinate => ENNReal.ofReal (z.1-z.2.1)*
      ENNReal.ofReal (prefixConeGood s T X z)) μ :=
    ((measurable_fst.sub (measurable_fst.comp measurable_snd)).ennreal_ofReal.mul hG.ennreal_ofReal).aemeasurable
  apply lintegral_product_bound_two μ hW hN
  · have hfield := hs.physicalBin_goodField hT hX hV C k j hJ hI hangle
    apply le_trans _ hfield
    apply le_of_eq
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV C measurableSet_Icc)
    intro z hz
    have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
    have hg : 0≤prefixConeGood s T X z := add_nonneg (norm_nonneg _) (abs_nonneg _)
    dsimp only
    rw [mul_pow,← ENNReal.ofReal_pow hr,← ENNReal.ofReal_pow hg,← ENNReal.ofReal_mul (sq_nonneg _)]
  · apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV C measurableSet_Icc)
    intro z hz
    exact hbound X V C z.1 z.2.1 z.2.2 P θ σ
      ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩ hP.le hθ hσ hq hd he
  · have hmass := F.physicalBin_weighted_occupation hs hT zX C hS hS0 hJ hR.le hD.le
    have hμ : physicalBinMeasure (fun t => (F.flow zX t).2) C (Icc a b) = μ := by
      unfold μ physicalBinMeasure V
      rw [physicalBinBase_prefix zX C hJ]
    rw [hμ] at hmass
    have hne : ENNReal.ofReal (C.rmin^2*C.Dmin)≠0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    apply (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top)).mpr
    rw [mul_comm]
    convert hmass using 1
    congr 1
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV C measurableSet_Icc)
    intro z hz
    simp only [N,X,V,physicalBinDensity,prefixFlow,prefixClamp_eq (hJ hz.1)]
  · exact physicalBinMeasure_volume hV C measurableSet_Icc hφ hDmax

end RVM

end

end OAI
