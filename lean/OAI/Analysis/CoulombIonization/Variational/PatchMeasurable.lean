import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped ENNReal

namespace CoulombAnalysis

lemma measurable_of_distance_functions {α β : Type*} [MeasurableSpace α]
    [MetricSpace β] [SecondCountableTopology β] [MeasurableSpace β] [BorelSpace β]
    {f : α → β} (hf : ∀ z, Measurable (fun x => dist (f x) z)) : Measurable f := by
  let S : Set (Set β) := {u | ∃ z r, u = ball z r}
  have hb : IsTopologicalBasis S := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro u ⟨z,r,rfl⟩
      exact isOpen_ball
    · intro z u hzu hu
      obtain ⟨r,hr,hs⟩ := Metric.isOpen_iff.mp hu z hzu
      exact ⟨ball z r,⟨z,r,rfl⟩,mem_ball_self hr,hs⟩
  rw [‹BorelSpace β›.measurable_eq]
  change @Measurable α β _ (borel β) f
  rw [hb.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro u ⟨z,r,rfl⟩
  exact measurableSet_lt (hf z) measurable_const

local instance {β : Type*} [MeasurableSpace β] (μ : Measure β) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    MeasurableSpace (Lp ℝ p μ) := borel _
local instance {β : Type*} [MeasurableSpace β] (μ : Measure β) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    BorelSpace (Lp ℝ p μ) := ⟨rfl⟩

lemma measurable_memLp_toLp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure β} [SFinite μ] {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ⊤)]
    [SecondCountableTopology (Lp ℝ p μ)] {f : α → β → ℝ}
    (hf : Measurable (Function.uncurry f)) (hp : ∀ a, MemLp (f a) p μ) :
    Measurable (fun a => (hp a).toLp (f a)) := by
  apply measurable_of_distance_functions
  intro z
  have hd : Measurable (fun q : α × β => f q.1 q.2-z q.2) :=
    hf.sub ((Lp.stronglyMeasurable z).measurable.comp measurable_snd)
  have hslice (point : α) : AEStronglyMeasurable (fun x => f point x-z x) μ :=
    (hd.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hh : Measurable (fun a => eLpNorm (fun x => f a x-z x) p μ) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) (Fact.out : p ≠ ⊤)
      (hslice _)]
    exact ((hd.enorm.pow_const p.toReal).lintegral_prod_right').pow_const _
  convert hh.ennreal_toReal using 1
  funext a
  rw [Lp.dist_def]
  congr 1
  apply eLpNorm_congr_ae
  exact (hp a).coeFn_toLp.sub ae_eq_rfl

def toLpOrZero {α β : Type*} [MeasurableSpace β] (μ : Measure β) (p : ℝ≥0∞)
    (f : α → β → ℝ) (a : α) : Lp ℝ p μ :=
  by
    classical
    exact if h : MemLp (f a) p μ then h.toLp (f a) else 0

lemma toLpOrZero_eq {α β : Type*} [MeasurableSpace β] {μ : Measure β}
    {p : ℝ≥0∞} {f : α → β → ℝ} {a : α} (h : MemLp (f a) p μ) :
    toLpOrZero μ p f a = h.toLp (f a) := by simp [toLpOrZero,h]

lemma toLpOrZero_congr {α β : Type*} [MeasurableSpace β] {μ : Measure β}
    {p : ℝ≥0∞} {f g : α → β → ℝ} {a : α} (h : f a =ᵐ[μ] g a) :
    toLpOrZero μ p f a = toLpOrZero μ p g a := by
  by_cases hf : MemLp (f a) p μ
  · have hg := (memLp_congr_ae h).mp hf
    rw [toLpOrZero_eq hf,toLpOrZero_eq hg]
    exact MemLp.toLp_congr hf hg h
  · have hg : ¬ MemLp (g a) p μ := fun hg => hf ((memLp_congr_ae h).mpr hg)
    simp [toLpOrZero,hf,hg]

lemma measurable_toLpOrZero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure β} [SFinite μ] {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ⊤)]
    [SecondCountableTopology (Lp ℝ p μ)] {f : α → β → ℝ}
    (hf : Measurable (Function.uncurry f)) : Measurable (toLpOrZero μ p f) := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hm (a : α) : AEStronglyMeasurable (f a) μ :=
    (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hn : Measurable (fun a => eLpNorm (f a) p μ) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 (Fact.out : p ≠ ⊤) (hm _)]
    exact ((hf.enorm.pow_const p.toReal).lintegral_prod_right').pow_const _
  let E : Set α := {a | eLpNorm (f a) p μ < ⊤}
  have hE : MeasurableSet E := measurableSet_lt hn measurable_const
  let g : α → β → ℝ := fun a => if a ∈ E then f a else 0
  have hg : Measurable (Function.uncurry g) := by
    convert (hf.piecewise (hE.preimage measurable_fst) (measurable_const (a := (0:ℝ)))) using 1
    funext q
    change (if q.1 ∈ E then f q.1 else 0) q.2 = if q.1 ∈ E then f q.1 q.2 else 0
    split <;> rfl
  have hp (a : α) : MemLp (g a) p μ := by
    by_cases ha : a ∈ E
    · simpa only [g,ite_eq_left ha] using (show MemLp (f a) p μ from ha)
    · simpa only [g,ite_eq_right ha] using (MemLp.zero : MemLp (0 : β → ℝ) p μ)
  have hh := measurable_memLp_toLp hg hp
  convert hh using 1
  funext a
  by_cases ha : a ∈ E
  · have hf' : MemLp (f a) p μ := ha
    rw [toLpOrZero_eq hf']
    apply Lp.ext
    have he : (hp a).toLp (g a) =ᵐ[μ] f a := by
      simpa only [g,ite_eq_left ha] using (hp a).coeFn_toLp
    exact hf'.coeFn_toLp.trans he.symm
  · have hf' : ¬ MemLp (f a) p μ := fun hf' => ha hf'
    simp only [toLpOrZero,dite_eq_right hf']
    apply Lp.ext
    have he : (hp a).toLp (g a) =ᵐ[μ] (0 : β → ℝ) := by
      simpa only [g,ite_eq_right ha] using (hp a).coeFn_toLp
    exact (Lp.coeFn_zero ℝ p μ).trans he.symm

lemma aemeasurable_toLpOrZero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} {μ : Measure β} [SFinite μ] [SFinite ν]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ⊤)]
    [SecondCountableTopology (Lp ℝ p μ)] {f : α → β → ℝ}
    (hf : AEStronglyMeasurable (Function.uncurry f) (ν.prod μ)) :
    AEMeasurable (toLpOrZero μ p f) ν := by
  let g : α → β → ℝ := fun a b => hf.mk (Function.uncurry f) (a,b)
  have hg : Measurable (Function.uncurry g) := hf.stronglyMeasurable_mk.measurable
  apply (measurable_toLpOrZero hg).aemeasurable.congr
  filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk] with a ha
  exact (toLpOrZero_congr (f := f) (g := g) (a := a) ha).symm

end CoulombAnalysis

end

end OAI
