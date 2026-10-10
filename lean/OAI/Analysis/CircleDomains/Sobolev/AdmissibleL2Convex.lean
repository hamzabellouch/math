import OAI.Analysis.CircleDomains.Probability.MeasureFamilyDominatedLimit
import Mathlib.Analysis.Convex.Basic

namespace OAI

/-! Convexity of the actual L² classes with a nonnegative Borel,
pointwise-admissible representative for a specified family. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def admissibleL2Classes {A Z : Type*} [MeasurableSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) : Set (Lp ℝ 2 σ) :=
  {v | ∃ f : Z → ℝ, ∃ hf : MemLp f 2 σ, Measurable f ∧ (∀ z, 0 ≤ f z) ∧
    (∀ a, 1 ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂(K a : Measure Z)) ∧ hf.toLp f = v}

lemma admissibleL2Classes_convex {A Z : Type*} [MeasurableSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) : Convex ℝ (admissibleL2Classes σ K) := by
  intro v hv w hw a b ha hb hab
  obtain ⟨f,hf,hfm,hf0,hfa,rfl⟩ := hv
  obtain ⟨g,hg,hgm,hg0,hga,rfl⟩ := hw
  let h : Z → ℝ := fun z => a*f z+b*g z
  have hL : MemLp h 2 σ := (hf.const_mul a).add (hg.const_mul b)
  refine ⟨h,hL,measurable_const.mul hfm |>.add (measurable_const.mul hgm),
    fun z => add_nonneg (mul_nonneg ha (hf0 z)) (mul_nonneg hb (hg0 z)),?_,?_⟩
  · intro i
    have he : (fun z => ENNReal.ofReal (h z)) = fun z =>
        ENNReal.ofReal a * ENNReal.ofReal (f z) +
          ENNReal.ofReal b * ENNReal.ofReal (g z) := by
      funext z
      dsimp only [h]
      rw [ENNReal.ofReal_add (mul_nonneg ha (hf0 z)) (mul_nonneg hb (hg0 z)),
        ENNReal.ofReal_mul ha,ENNReal.ofReal_mul hb]
    rw [he]
    have hadd := lintegral_add_left (μ := (K i : Measure Z))
      (f := fun z => ENNReal.ofReal a * ENNReal.ofReal (f z))
      (g := fun z => ENNReal.ofReal b * ENNReal.ofReal (g z))
      (measurable_const.mul hfm.ennreal_ofReal)
    rw [hadd,lintegral_const_mul _ hfm.ennreal_ofReal,
      lintegral_const_mul _ hgm.ennreal_ofReal]
    calc
      (1 : ℝ≥0∞) = ENNReal.ofReal a + ENNReal.ofReal b := by
        rw [← ENNReal.ofReal_add ha hb,hab,ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal a * ∫⁻ z, ENNReal.ofReal (f z) ∂(K i : Measure Z) +
          ENNReal.ofReal b * ∫⁻ z, ENNReal.ofReal (g z) ∂(K i : Measure Z) := by
        simpa only [mul_one] using add_le_add
          (mul_le_mul_right (hfa i) (ENNReal.ofReal a))
          (mul_le_mul_right (hga i) (ENNReal.ofReal b))
  · apply Lp.ext
    filter_upwards [hL.coeFn_toLp,hf.coeFn_toLp,hg.coeFn_toLp,
      Lp.coeFn_add (a • hf.toLp f) (b • hg.toLp g),
      Lp.coeFn_smul a (hf.toLp f),Lp.coeFn_smul b (hg.toLp g)] with z hz hfz hgz habz haz hbz
    rw [hz,habz]
    simp only [Pi.add_apply]
    rw [haz,hbz]
    simp only [Pi.smul_apply,smul_eq_mul,hfz,hgz]
    rfl

end CircleDomainRigidity

end

end OAI
