import OAI.Analysis.LipschitzHilbert.Estimates.CompactMollificationSupport
import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Gram

namespace OAI

/-! Bounded measurable restricted tests admit unit-bounded Schwartz
approximants in every open neighbourhood of their finite-measure support. -/
noncomputable section
open MeasureTheory Function Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem restrictedTest_integrable (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f)
    (hb : ∀ z, ‖f z‖≤1) (A : Set (ℝ×ℝ)) (hA : MeasurableSet A)
    (hAfin : planeMeasure A≠∞) (hsupp : support f⊆A) : Integrable f planeMeasure := by
  have hi : Integrable (A.indicator (fun _ : ℝ×ℝ => (1:ℝ))) planeMeasure :=
    (integrableOn_const hAfin).integrable_indicator hA
  apply hi.mono' hfm.aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : z∈A
  · simpa only [Set.indicator_of_mem hz] using hb z
  · have hzero : f z=0 := notMem_support.mp (fun h => hz (hsupp h))
    simp only [Set.indicator_of_notMem hz,hzero,norm_zero,le_refl]

theorem restrictedTest_cutoff_pointwise (f : (ℝ×ℝ) → ℂ)
    (hb : ∀ z, ‖f z‖≤1) (A K : Set (ℝ×ℝ)) (hsupp : support f⊆A) (z : ℝ×ℝ) :
    ‖K.indicator f z-f z‖^2≤(A\K).indicator (fun _ : ℝ×ℝ => (1:ℝ)) z := by
  by_cases hzK : z∈K
  · simp only [Set.indicator_of_mem hzK,sub_self,norm_zero,zero_pow (by decide : 2≠0)]
    exact indicator_nonneg (fun _ _ => by norm_num) _
  · rw [Set.indicator_of_notMem hzK]
    by_cases hzA : z∈A
    · rw [Set.indicator_of_mem (show z∈A\K from ⟨hzA,hzK⟩)]
      simpa only [zero_sub,norm_neg,one_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (hb z) 2
    · have hzero : f z=0 := notMem_support.mp (fun h => hzA (hsupp h))
      simp only [hzero,sub_self,norm_zero,zero_pow (by decide : 2≠0)]
      exact indicator_nonneg (fun _ _ => by norm_num) _

theorem restrictedTest_compact_integral_error (f : (ℝ×ℝ) → ℂ)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure)
    (A K : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hK : MeasurableSet K) (hsupp : support f⊆A) :
    (∫ z, ‖K.indicator f z-f z‖^2 ∂planeMeasure)≤planeMeasure.real (A\K) := by
  have hdiff : MeasurableSet (A\K) := hA.diff hK
  have hdiffFin : planeMeasure (A\K)≠∞ :=
    ne_top_of_le_ne_top hAfin (measure_mono sdiff_subset)
  have hi : Integrable ((A\K).indicator (fun _ : ℝ×ℝ => (1:ℝ))) planeMeasure :=
    (integrableOn_const hdiffFin).integrable_indicator hdiff
  have hierr : Integrable (fun z => ‖K.indicator f z-f z‖^2) planeMeasure :=
    (memLp_two_iff_integrable_sq_norm ((hf2.indicator hK).sub hf2).aestronglyMeasurable).mp
      ((hf2.indicator hK).sub hf2)
  calc
    _ ≤ ∫ z, (A\K).indicator (fun _ : ℝ×ℝ => (1:ℝ)) z ∂planeMeasure :=
      integral_mono hierr hi (restrictedTest_cutoff_pointwise f hb A K hsupp)
    _ = _ := by simpa only [smul_eq_mul,mul_one] using integral_indicator_const (1:ℝ) hdiff

theorem restrictedTest_compact_error (f : (ℝ×ℝ) → ℂ)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure)
    (A K : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hK : MeasurableSet K) (hsupp : support f⊆A) :
    ‖(hf2.indicator hK).toLp (K.indicator f)-hf2.toLp f‖^2≤planeMeasure.real (A\K) := by
  have heq := MemLp.toLp_sub (f:=K.indicator f) (g:=f) (hf2.indicator hK) hf2
  rw [←heq,memLp_toL2_norm_sq]
  exact restrictedTest_compact_integral_error f hb hf2 A K hA hAfin hK hsupp

theorem exists_schwartz_approx_restricted (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure)
    (A U : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hsupp : support f⊆A) (hU : IsOpen U) (hAU : A⊆U) (epsilon : ℝ) (he : 0<epsilon) :
    ∃ g : SchwartzMap (ℝ×ℝ) ℂ, (∀ z, ‖g z‖≤1) ∧ support g⊆U ∧
      ‖g.toLp 2 planeMeasure-hf2.toLp f‖<epsilon := by
  have hehalf : 0<epsilon/2 := by positivity
  obtain ⟨K,hKA,hK,herror⟩ := hA.exists_isCompact_sdiff_lt hAfin
    (by positivity : ENNReal.ofReal ((epsilon/2)^2)≠0)
  have hf := restrictedTest_integrable f hfm hb A hA hAfin hsupp
  let fK := K.indicator f
  have hfKm : Measurable fK := hfm.indicator hK.measurableSet
  have hfKi : Integrable fK planeMeasure := hf.indicator hK.measurableSet
  have hfK2 : MemLp fK 2 planeMeasure := hf2.indicator hK.measurableSet
  have hfKs : support fK⊆K := by
    intro z hz
    by_contra hn
    exact hz (Set.indicator_of_notMem hn f)
  have hfKc : HasCompactSupport fK := hK.of_isClosed_subset isClosed_closure
    (closure_minimal (hfKs) hK.isClosed)
  have hfKb (z) : ‖fK z‖≤1 := by
    by_cases hz : z∈K
    · simpa only [fK,Set.indicator_of_mem hz] using hb z
    · simp only [fK,Set.indicator_of_notMem hz,norm_zero,zero_le_one]
  have hKfin : planeMeasure (A\K)≠∞ := ne_top_of_le_ne_top hAfin (measure_mono sdiff_subset)
  have herrReal : planeMeasure.real (A\K)<(epsilon/2)^2 := by
    exact (ENNReal.toReal_lt_toReal hKfin ENNReal.ofReal_ne_top).2 herror |>.trans_eq
      (ENNReal.toReal_ofReal (sq_nonneg _))
  have hnorm : ‖hfK2.toLp fK-hf2.toLp f‖<epsilon/2 := by
    have hsquare := (restrictedTest_compact_error f hb hf2 A K hA hAfin hK.measurableSet hsupp).trans_lt herrReal
    exact (sq_lt_sq₀ (norm_nonneg _) hehalf.le).1 hsquare
  obtain ⟨g,hgb,hgs,hgclose⟩ := exists_schwartz_approx_compact fK hfKm hfKi hfKc hfKb hfK2
    K U hK (hfKs) hU (hKA.trans hAU) (epsilon/2) hehalf
  refine ⟨g,hgb,hgs,?_⟩
  have htri := norm_add_le (g.toLp 2 planeMeasure-hfK2.toLp fK) (hfK2.toLp fK-hf2.toLp f)
  rw [sub_add_sub_cancel] at htri
  linarith only [htri,hgclose,hnorm]

end LipschitzHilbert.PacketRepresentation

end

end OAI
