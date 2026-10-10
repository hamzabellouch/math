import OAI.Analysis.IrrationalRotation.Model.ProductSampling
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.TailTrimming

theorem exists_dominated_l2_density {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [IsFiniteMeasure μ]
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hν : ν ≤ μ.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∃ g : Lp ℝ 2 μ,
      (∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ f x) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (g x)) ∧ ‖g‖ ≤ ‖f‖ := by
  have : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) :=
    isFiniteMeasure_withDensity_ofReal ((Lp.memLp f).integrable (by norm_num)).2
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le _ hν
  have hac : ν ≪ μ := hν.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hbound : ν.rnDeriv μ ≤ᵐ[μ] (fun x => ENNReal.ofReal (f x)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν μ)
    intro s hs _hfinite
    exact (Measure.setLIntegral_rnDeriv_le s).trans
      ((hν s).trans_eq (withDensity_apply _ hs))
  let d : X → ℝ := fun x => (ν.rnDeriv μ x).toReal
  have hd0 (x : X) : 0 ≤ d x := ENNReal.toReal_nonneg
  have hdmeas : AEStronglyMeasurable d μ :=
    (Measure.measurable_rnDeriv ν μ).ennreal_toReal.aestronglyMeasurable
  have hdle : ∀ᵐ x ∂μ, d x ≤ f x := by
    filter_upwards [hbound, hf] with x hx hx0
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hx
    simpa only [ENNReal.toReal_ofReal hx0] using h
  have hd : MemLp d 2 μ := by
    apply (Lp.memLp f).mono' hdmeas
    filter_upwards [hdle] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hd0 x)] using hx
  let g : Lp ℝ 2 μ := hd.toLp d
  have hgeq : (fun x => g x) =ᵐ[μ] d := hd.coeFn_toLp
  refine ⟨g, ?_, ?_, ?_⟩
  · filter_upwards [hgeq, hdle] with x hx hxle
    rw [hx]
    exact ⟨ENNReal.toReal_nonneg, hxle⟩
  · calc
      ν = μ.withDensity (ν.rnDeriv μ) := (Measure.withDensity_rnDeriv_eq ν μ hac).symm
      _ = μ.withDensity (fun x => ENNReal.ofReal (g x)) := by
        apply withDensity_congr_ae
        filter_upwards [hgeq, hbound] with x hx hxb
        rw [hx]
        exact (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxb)).symm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hgeq, hdle, hf] with x hx hxle hx0
    rw [hx]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hd0 x),
      abs_of_nonneg hx0] using hxle

end Invariant233.TailTrimming

namespace Invariant233.ProductModel

theorem HasUniformL2Marginals.isFiniteMeasure {η : ℕ → Measure EndpointPair}
    (hη : HasUniformL2Marginals η) (l : ℕ) : IsFiniteMeasure (η l) := by
  obtain ⟨H, hH, hη⟩ := hη
  obtain ⟨f, g, hf0, hg0, hf, hg, hfH, hgH⟩ := hη l
  have : IsFiniteMeasure (baseMeasure.withDensity (fun x => ENNReal.ofReal (f x))) :=
    isFiniteMeasure_withDensity_ofReal ((Lp.memLp f).integrable (by norm_num)).2
  have : IsFiniteMeasure ((η l).map Prod.fst) := by
    rw [hf]
    infer_instance
  exact Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable

theorem HasUniformL2Marginals.mono {η ζ : ℕ → Measure EndpointPair}
    (hη : HasUniformL2Marginals η) (hζ : ∀ l, ζ l ≤ η l) :
    HasUniformL2Marginals ζ := by
  obtain ⟨H, hH, hη⟩ := hη
  refine ⟨H, hH, ?_⟩
  intro l
  obtain ⟨f, g, hf0, hg0, hf, hg, hfH, hgH⟩ := hη l
  have hfst : (ζ l).map Prod.fst ≤
      baseMeasure.withDensity (fun x => ENNReal.ofReal (f x)) := by
    rw [← hf]
    exact Measure.map_mono (hζ l) measurable_fst
  have hsnd : (ζ l).map Prod.snd ≤
      baseMeasure.withDensity (fun x => ENNReal.ofReal (g x)) := by
    rw [← hg]
    exact Measure.map_mono (hζ l) measurable_snd
  obtain ⟨f', hf'0, hf', hf'norm⟩ :=
    Invariant233.TailTrimming.exists_dominated_l2_density f hf0 hfst
  obtain ⟨g', hg'0, hg', hg'norm⟩ :=
    Invariant233.TailTrimming.exists_dominated_l2_density g hg0 hsnd
  exact ⟨f', g', hf'0.mono (fun _ h => h.1), hg'0.mono (fun _ h => h.1),
    hf', hg', hf'norm.trans hfH, hg'norm.trans hgH⟩

theorem HasUniformL2Marginals.restrict {η : ℕ → Measure EndpointPair}
    (hη : HasUniformL2Marginals η) (S : ℕ → Set EndpointPair) :
    HasUniformL2Marginals (fun l => (η l).restrict (S l)) :=
  hη.mono (fun _ => Measure.restrict_le_self)

end Invariant233.ProductModel

end

end OAI
