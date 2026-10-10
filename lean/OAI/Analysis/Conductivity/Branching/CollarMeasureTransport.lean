import Mathlib
import OAI.Analysis.Conductivity.Geometry.CollarReverseBound

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma finiteMeasure_le_of_nonneg_compact_integrals
    {n : ℕ} {μ ν : Measure (Fin n → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : (Fin n → ℝ) → ℝ, Continuous f → HasCompactSupport f →
      (∀ x,0≤f x) → (∫ x,f x ∂μ)≤∫ x,f x ∂ν) : μ≤ν := by
  have hc (K : Set (Fin n → ℝ)) (hK : IsCompact K) : μ K≤ν K := by
    rw [hK.measure_eq_biInf_integral_hasCompactSupport ν]
    simp only [le_iInf_iff]
    intro f hf hcomp hKf hn
    exact ((hf.integrable_of_hasCompactSupport hcomp).measure_le_integral
      (Eventually.of_forall hn) (fun x hx => by simp [hKf hx])).trans
      (ENNReal.ofReal_le_ofReal (h f hf hcomp hn))
  apply Measure.le_iff.mpr
  intro s hs
  rw [hs.measure_eq_iSup_isCompact_of_ne_top (measure_ne_top μ s)]
  simp only [iSup_le_iff]
  intro K hKs hK
  exact (hc K hK).trans (measure_mono hKs)

def sourcePhysicalCollarMeasure (l r : ℝ) : Measure (Fin 3 → ℝ) :=
  ∑ i : Fin 4,∑ j : Fin 4,volume.restrict (sourceCollarPiece i j '' sourceExtendedBox l r)

def sourceAngularCollarMeasure (l r : ℝ) : Measure (Fin 3 → ℝ) :=
  Measure.map (Function.uncurry sourceAngularCollar)
    ((volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2))))

lemma continuous_uncurry_sourceAngularCollar : Continuous (Function.uncurry sourceAngularCollar) := by
  change Continuous (fun z : ℝ×UnitAddTorus (Fin 2) => sourceAngularCollar z.1 z.2)
  simpa only [zero_add] using continuous_sourceAngular 0

instance sourcePhysicalCollarMeasure_finite (l r : ℝ) :
    IsFiniteMeasure (sourcePhysicalCollarMeasure l r) := by
  have (i j : Fin 4) : IsFiniteMeasure
      (volume.restrict (sourceCollarPiece i j '' sourceExtendedBox l r)) :=
    ⟨by simpa only [Measure.restrict_apply_univ,sourceExtendedBox] using (isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous).measure_lt_top⟩
  unfold sourcePhysicalCollarMeasure
  infer_instance

instance sourceAngularCollarMeasure_finite (l r : ℝ) :
    IsFiniteMeasure (sourceAngularCollarMeasure l r) := by
  unfold sourceAngularCollarMeasure
  infer_instance

lemma integral_sourcePhysicalCollarMeasure {f : (Fin 3 → ℝ) → ℝ}
    (hf : Continuous f) (l r : ℝ) :
    (∫ x,f x ∂sourcePhysicalCollarMeasure l r)=
      ∑ i : Fin 4,∑ j : Fin 4,∫ x in sourceCollarPiece i j '' sourceExtendedBox l r,f x := by
  have hi (i j : Fin 4) : IntegrableOn f (sourceCollarPiece i j '' sourceExtendedBox l r) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous)
  unfold sourcePhysicalCollarMeasure
  rw [integral_finsetSum_measure (fun i _ => integrable_finsetSum_measure.mpr (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum_measure (fun j _ => hi i j)

lemma integral_sourceAngularCollarMeasure {f : (Fin 3 → ℝ) → ℝ}
    (hf : Continuous f) {l r : ℝ} (hlr : l≤r) :
    (∫ x,f x ∂sourceAngularCollarMeasure l r)=
      ∫ t in l..r,∫ θ : UnitAddTorus (Fin 2),f (sourceAngularCollar t θ) := by
  unfold sourceAngularCollarMeasure
  rw [integral_map continuous_uncurry_sourceAngularCollar.aemeasurable hf.aestronglyMeasurable]
  have hi : Integrable (fun p : ℝ×UnitAddTorus (Fin 2) => f (sourceAngularCollar p.1 p.2))
      ((volume.restrict (Ioc l r)).prod volume) := by
    have hh := (hf.comp continuous_uncurry_sourceAngularCollar).continuousOn.integrableOn_compact (μ:=volume)
      ((isCompact_Icc : IsCompact (Icc l r)).prod (isCompact_univ : IsCompact (univ : Set (UnitAddTorus (Fin 2)))))
    have hh' := hh.mono_set (prod_mono Ioc_subset_Icc_self Subset.rfl)
    simpa only [Function.comp_def,Function.uncurry_def,IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict,Measure.restrict_univ] using hh'
  simp only [Function.uncurry]
  rw [integral_prod _ hi,intervalIntegral.integral_of_le hlr]

theorem sourcePhysicalCollarMeasure_le {l r : ℝ}
    (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    sourcePhysicalCollarMeasure l r ≤
      ENNReal.ofReal (2/(faceRayDensityLower 1*faceRayDensityLower sourceRadialWidth)) •
        sourceAngularCollarMeasure l r := by
  have : IsFiniteMeasure
      (ENNReal.ofReal (2/(faceRayDensityLower 1*faceRayDensityLower sourceRadialWidth)) •
        sourceAngularCollarMeasure l r) :=
    ⟨by
      rw [Measure.smul_apply]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  apply finiteMeasure_le_of_nonneg_compact_integrals
  intro f hf hcomp hn
  rw [integral_sourcePhysicalCollarMeasure hf,integral_smul_measure,
    ENNReal.toReal_ofReal (by
      have h0 := faceRayDensityLower_pos (w:=1) (by norm_num)
      have h1 := faceRayDensityLower_pos (w:=sourceRadialWidth)
        (by norm_num [sourceRadialWidth,sourceHole])
      positivity),integral_sourceAngularCollarMeasure hf hlr]
  exact sourceAngular_volume_reverse hf hn hlr hl hr

theorem sourceAngularCollarMeasure_le {l r : ℝ}
    (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    sourceAngularCollarMeasure l r ≤
      ENNReal.ofReal (100*((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi))) •
        sourcePhysicalCollarMeasure l r := by
  have : IsFiniteMeasure
      (ENNReal.ofReal (100*((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi))) •
        sourcePhysicalCollarMeasure l r) :=
    ⟨by
      rw [Measure.smul_apply]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  apply finiteMeasure_le_of_nonneg_compact_integrals
  intro f hf hcomp hn
  rw [integral_sourceAngularCollarMeasure hf hlr,integral_smul_measure,
    ENNReal.toReal_ofReal (by norm_num [sourceRadialWidth,sourceHole]; positivity),
    integral_sourcePhysicalCollarMeasure hf]
  exact sourceAngular_volume_bound hf hn hlr hl hr

theorem sourcePhysical_memLp_of_angular {E : Type*} [NormedAddCommGroup E]
    {g : (Fin 3 → ℝ) → E} (hg : StronglyMeasurable g) {p : ℝ≥0∞} {l r : ℝ}
    (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hm : MemLp (g ∘ Function.uncurry sourceAngularCollar) p
      ((volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2))))) :
    MemLp g p (sourcePhysicalCollarMeasure l r) := by
  have H : MemLp g p (sourceAngularCollarMeasure l r) :=
    (memLp_map_measure_iff hg.aestronglyMeasurable
      continuous_uncurry_sourceAngularCollar.aemeasurable).mpr hm
  exact H.of_measure_le_smul ENNReal.ofReal_ne_top (sourcePhysicalCollarMeasure_le hlr hl hr)

theorem sourceCollar_ae_iff {l r : ℝ}
    (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    {P : (Fin 3 → ℝ) → Prop} :
    (∀ᵐ y∂sourcePhysicalCollarMeasure l r,P y) ↔
      ∀ᵐ y∂sourceAngularCollarMeasure l r,P y := by
  exact ⟨fun h => h.filter_mono (Measure.absolutelyContinuous_of_le_smul
      (sourceAngularCollarMeasure_le hlr hl hr)).ae_le,
    fun h => h.filter_mono (Measure.absolutelyContinuous_of_le_smul
      (sourcePhysicalCollarMeasure_le hlr hl hr)).ae_le⟩

end ScalarConductivity

end

end OAI
