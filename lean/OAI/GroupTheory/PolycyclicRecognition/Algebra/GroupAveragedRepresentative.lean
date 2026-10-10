import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.WithDensityFinite

namespace OAI

/-! # Exactly invariant representatives from group averaging

A probability equivalent to Haar measure is quasi-preserved by every right
translation. On the invariant measurable set where an orbit function is
essentially constant, its group integral is that constant. Assigning zero on
the complement gives a measurable, everywhere invariant representative.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set Filter

variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace X]
  [MulAction G X] (η : Measure G) [IsProbabilityMeasure η]

def groupAverage (f : X → ℝ) (x : X) : ℝ := ∫ g, f (g • x) ∂η

def groupAverageGood (f : X → ℝ) : Set X :=
  {x | ∀ᵐ g ∂η, f (g • x) = groupAverage η f x}

theorem measurable_groupAverage (f : X → ℝ)
    (hf : Measurable (fun p : X × G => f (p.2 • p.1))) :
    Measurable (groupAverage η f) :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

theorem measurableSet_groupAverageGood (f : X → ℝ)
    (hf : Measurable (fun p : X × G => f (p.2 • p.1))) :
    MeasurableSet (groupAverageGood η f) := by
  have hm := measurable_groupAverage η f hf
  have hs : MeasurableSet {p : X × G | f (p.2 • p.1) ≠ groupAverage η f p.1} :=
    (measurableSet_eq_fun hf (hm.comp measurable_fst)).compl
  have hmass := measurable_measure_prodMk_left (ν := η) hs
  have he : groupAverageGood η f =
      {x | η (Prod.mk x ⁻¹' {p : X × G | f (p.2 • p.1) ≠ groupAverage η f p.1}) = 0} := by
    ext x
    simp only [groupAverageGood, mem_ofPred_eq, measure_eq_zero_iff_ae_notMem,
      mem_preimage, not_not]
  rw [he]
  exact measurableSet_eq_fun hmass measurable_const

omit [MeasurableSpace X] in
theorem groupAverageGood_smul (f : X → ℝ)
    (hq : ∀ h : G, QuasiMeasurePreserving (fun g => g * h) η η)
    {x : X} (hx : x ∈ groupAverageGood η f) (h : G) :
    h • x ∈ groupAverageGood η f ∧ groupAverage η f (h • x) = groupAverage η f x := by
  have he : ∀ᵐ g ∂η, f (g • (h • x)) = groupAverage η f x := by
    simpa only [mul_smul] using (hq h).ae hx
  have hav : groupAverage η f (h • x) = groupAverage η f x := by
    rw [groupAverage, integral_congr_ae he]
    simp
  exact ⟨by simpa only [groupAverageGood, mem_ofPred_eq, hav] using he, hav⟩

theorem measurable_invariantRepresentative_of_groupAverage
    (hq : ∀ h : G, QuasiMeasurePreserving (fun g => g * h) η η)
    (μ : Measure X) [SFinite μ] (f : X → ℝ) (hf : Measurable f)
    (ha : Measurable (fun p : G × X => p.1 • p.2))
    (hi : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] f) :
    ∃ F : X → ℝ, Measurable F ∧ F =ᵐ[μ] f ∧ ∀ (g : G) x, F (g • x) = F x := by
  have hfx : Measurable (fun p : X × G => f (p.2 • p.1)) :=
    (hf.comp ha).comp measurable_swap
  let S := groupAverageGood η f
  let F := S.indicator (groupAverage η f)
  have hSm : MeasurableSet S := measurableSet_groupAverageGood η f hfx
  have haex : ∀ᵐ x ∂μ, ∀ᵐ g ∂η, f (g • x) = f x := by
    apply (Measure.ae_ae_comm (μ := η) (ν := μ)
      (measurableSet_eq_fun (hf.comp ha) (hf.comp measurable_snd))).1
    exact Filter.Eventually.of_forall hi
  refine ⟨F, (measurable_groupAverage η f hfx).indicator hSm, ?_, ?_⟩
  · filter_upwards [haex] with x hx
    have hav : groupAverage η f x = f x := by
      rw [groupAverage, integral_congr_ae hx]
      simp
    have hS : x ∈ S := by
      change ∀ᵐ g ∂η, f (g • x) = groupAverage η f x
      simpa only [hav] using hx
    simp only [F, indicator_of_mem hS, hav]
  · intro g x
    by_cases hx : x ∈ S
    · obtain ⟨hg, he⟩ := groupAverageGood_smul η f hq hx g
      change g • x ∈ S at hg
      simp only [F, indicator_of_mem hx, indicator_of_mem hg, he]
    · have hg : g • x ∉ S := by
        intro h
        have hh := (groupAverageGood_smul η f hq h g⁻¹).1
        exact hx (by simpa only [inv_smul_smul] using hh)
      simp only [F, indicator_of_notMem hx, indicator_of_notMem hg]

end PolycyclicRecognition

end

end OAI
