import OAI.Analysis.LipschitzHilbert.Estimates.AllDyadicWeakL1
import OAI.Analysis.LipschitzHilbert.Trees.SourceThreeGridMaximal

namespace OAI

/-! A genuine all-interval maximal majorant with a weak L1 estimate.
Only three fixed dyadic grids are used, with no scale cutoff. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.DyadicLineGrid

def threeGridSup (f : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  Finset.univ.sup (fun q : GridChoice => allDyadicSup q.val f x)

theorem threeGridSup_measurable (f : ℝ → ℝ) : Measurable (threeGridSup f) := by
  have h (s : Finset GridChoice) : Measurable (fun x => s.sup (fun q => allDyadicSup q.val f x)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert q s hqs ih =>
      simpa only [Finset.sup_insert] using (allDyadicSup_measurable q.val f).max ih
  exact h Finset.univ

theorem allDyadicSup_le_threeGridSup (q : GridChoice) (f : ℝ → ℝ) (x : ℝ) :
    allDyadicSup q.val f x ≤ threeGridSup f x :=
  Finset.le_sup (f := fun q : GridChoice => allDyadicSup q.val f x) (Finset.mem_univ q)

theorem threeGridSup_weak_L1 {f : ℝ → ℝ} (hf : Integrable f volume) (t : ℝ) (ht : 0<t) :
    volume {x | ENNReal.ofReal t<threeGridSup f x} ≤ ENNReal.ofReal (3*t⁻¹*(∫ x, |f x|)) := by
  have hsub : {x | ENNReal.ofReal t<threeGridSup f x}⊆
      ⋃ q : GridChoice, {x | ENNReal.ofReal t<allDyadicSup q.val f x} := by
    intro x hx
    change ENNReal.ofReal t < Finset.univ.sup (fun q : GridChoice => allDyadicSup q.val f x) at hx
    obtain ⟨q,_,hq⟩ := Finset.lt_sup_iff.mp hx
    exact mem_iUnion.mpr ⟨q,hq⟩
  calc
    _  ≤  volume (⋃ q : GridChoice, {x | ENNReal.ofReal t<allDyadicSup q.val f x}) := measure_mono hsub
    _  ≤  ∑ q : GridChoice, volume {x | ENNReal.ofReal t<allDyadicSup q.val f x} :=
      measure_iUnion_fintype_le _ _
    _  ≤  ∑ _q : GridChoice, ENNReal.ofReal (t⁻¹*(∫ x, |f x|)) :=
      Finset.sum_le_sum (fun q _ => allDyadicSup_weak_L1 q.val hf t ht)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,gridChoice_card,nsmul_eq_mul]
      rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

theorem interval_average_le_threeGridSup {f : ℝ → ℝ} (hf : Integrable f volume)
    (hf0 : ∀ x, 0 ≤ f x) (c r : ℝ) (hr : 0<r) {x : ℝ} (hx : x∈Icc (c-r) (c+r)) :
    ENNReal.ofReal ((∫ y in Icc (c-r) (c+r), f y)/(2*r)) ≤ 6*threeGridSup f x := by
  obtain ⟨q,hq,k,j,hsub,hscale⟩ := exists_comparable_three_grid_cover c r hr
  let Q : GridChoice := ⟨q,hq⟩
  have hxcell := hsub hx
  have hI : (∫ y in Icc (c-r) (c+r), f y) ≤ ∫ y in cell q k j, f y :=
    setIntegral_mono_set hf.integrableOn (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hsub)
  have heq : (∫ y in cell q k j, f y)=scale k*cellMean q k f x := by
    unfold cellMean
    rw [index_eq_of_mem hxcell]
    field_simp [(scale_pos k).ne']
  have hm : 0 ≤ cellMean q k f x := div_nonneg (integral_nonneg hf0) (scale_pos k).le
  have hreal : (∫ y in Icc (c-r) (c+r), f y)/(2*r) ≤ 6*|cellMean q k f x| := by
    apply (div_le_iff₀ (by positivity : 0<2*r)).mpr
    calc
      _  ≤  scale k*cellMean q k f x := hI.trans_eq heq
      _  ≤  (12*r)*cellMean q k f x := mul_le_mul_of_nonneg_right hscale hm
      _ = _ := by rw [abs_of_nonneg hm]; ring
  calc
    _  ≤  ENNReal.ofReal (6*|cellMean q k f x|) := ENNReal.ofReal_le_ofReal hreal
    _ = 6*ENNReal.ofReal |cellMean q k f x| := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    _  ≤  _ := mul_le_mul' le_rfl ((cellMean_le_allDyadicSup q k f x).trans
      (allDyadicSup_le_threeGridSup Q f x))

end LipschitzHilbert.DyadicLineGrid

end

end OAI
