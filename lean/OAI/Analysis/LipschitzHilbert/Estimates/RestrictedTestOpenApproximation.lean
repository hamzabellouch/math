import OAI.Analysis.LipschitzHilbert.Estimates.RestrictedTestApproximation

namespace OAI

/-! Bounded Schwartz approximation with support measures converging to
the original measurable support, inside a fixed open ambient set. -/
noncomputable section
open MeasureTheory Function Set Filter
open scoped ENNReal Topology
namespace LipschitzHilbert.PacketRepresentation

theorem exists_open_approx_inside (A V : Set (ℝ×ℝ))
    (hAfin : planeMeasure A≠∞) (hV : IsOpen V) (hAV : A⊆V)
    (epsilon : ℝ) (he : 0<epsilon) :
    ∃ U : Set (ℝ×ℝ), IsOpen U ∧ A⊆U ∧ U⊆V ∧ planeMeasure U≠∞ ∧
      planeMeasure.real A≤planeMeasure.real U ∧
      planeMeasure.real U<planeMeasure.real A+epsilon := by
  obtain ⟨O,hAO,hO,hOm⟩ := A.exists_isOpen_lt_add (μ:=planeMeasure) hAfin
    (by positivity : ENNReal.ofReal epsilon≠0)
  have hOfin : planeMeasure O≠∞ := ne_top_of_lt
    (hOm.trans_le (le_of_lt (ENNReal.add_lt_top.mpr ⟨hAfin.lt_top,ENNReal.ofReal_lt_top⟩)))
  let U := O∩V
  have hAU : A⊆U := fun _ hz => ⟨hAO hz,hAV hz⟩
  have hUfin : planeMeasure U≠∞ := ne_top_of_le_ne_top hOfin (measure_mono inter_subset_left)
  have hupper : planeMeasure.real O<planeMeasure.real A+epsilon := by
    have ht := (ENNReal.toReal_lt_toReal hOfin (ENNReal.add_ne_top.mpr ⟨hAfin,ENNReal.ofReal_ne_top⟩)).2 hOm
    simpa only [Measure.real,ENNReal.toReal_add hAfin ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal he.le] using ht
  exact ⟨U,hO.inter hV,hAU,inter_subset_right,hUfin,
    measureReal_mono hAU hUfin,(measureReal_mono inter_subset_left hOfin).trans_lt hupper⟩

theorem exists_schwartz_open_approx (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure)
    (A V : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hsupp : support f⊆A) (hV : IsOpen V) (hfsV : support f⊆V) (epsilon : ℝ) (he : 0<epsilon) :
    ∃ (g : SchwartzMap (ℝ×ℝ) ℂ) (U : Set (ℝ×ℝ)),
      (∀ z, ‖g z‖≤1) ∧ support g⊆U ∧ IsOpen U ∧ A⊆U ∧ support g⊆V ∧
      planeMeasure U≠∞ ∧ planeMeasure.real A≤planeMeasure.real U ∧
      planeMeasure.real U<planeMeasure.real A+epsilon ∧
      ‖g.toLp 2 planeMeasure-hf2.toLp f‖<epsilon := by
  obtain ⟨U,hU,hAU,_,hUfin,hUlo,hUhi⟩ := exists_open_approx_inside A univ hAfin isOpen_univ (subset_univ A) epsilon he
  have hAVfin : planeMeasure (A∩V)≠∞ := ne_top_of_le_ne_top hAfin (measure_mono inter_subset_left)
  obtain ⟨g,hgb,hgs,hgn⟩ := exists_schwartz_approx_restricted f hfm hb hf2
    (A∩V) (U∩V) (hA.inter hV.measurableSet) hAVfin (subset_inter hsupp hfsV)
    (hU.inter hV) (inter_subset_inter_left V hAU) epsilon he
  exact ⟨g,U,hgb,hgs.trans inter_subset_left,hU,hAU,hgs.trans inter_subset_right,
    hUfin,hUlo,hUhi,hgn⟩

theorem exists_schwartz_open_approx_sequence (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure)
    (A V : Set (ℝ×ℝ)) (hA : MeasurableSet A) (hAfin : planeMeasure A≠∞)
    (hsupp : support f⊆A) (hV : IsOpen V) (hfsV : support f⊆V) :
    ∃ (g : ℕ → SchwartzMap (ℝ×ℝ) ℂ) (U : ℕ → Set (ℝ×ℝ)),
      (∀ n, (∀ z, ‖g n z‖≤1) ∧ support (g n)⊆U n ∧ IsOpen (U n) ∧
        A⊆U n ∧ support (g n)⊆V ∧ planeMeasure (U n)≠∞) ∧
      Tendsto (fun n => (g n).toLp 2 planeMeasure) atTop (𝓝 (hf2.toLp f)) ∧
      Tendsto (fun n => planeMeasure.real (U n)) atTop (𝓝 (planeMeasure.real A)) := by
  have he (n : ℕ) : 0<(1:ℝ)/((n:ℝ)+1) := by positivity
  choose g U hgb hgs hU hAU hUV hUfin hUlo hUhi hgn using
    (fun n : ℕ => exists_schwartz_open_approx f hfm hb hf2 A V hA hAfin hsupp hV hfsV
      ((1:ℝ)/((n:ℝ)+1)) (he n))
  refine ⟨g,U,(fun n => ⟨hgb n,hgs n,hU n,hAU n,hUV n,hUfin n⟩),?_,?_⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa only [dist_eq_norm] using (hgn n).le
  · have hup : Tendsto (fun n : ℕ => planeMeasure.real A+1/((n:ℝ)+1))
        atTop (𝓝 (planeMeasure.real A)) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x:=planeMeasure.real A)).add tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hUlo (fun n => (hUhi n).le)

end LipschitzHilbert.PacketRepresentation

end

end OAI
