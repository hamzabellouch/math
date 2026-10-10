import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineNesting
import OAI.Analysis.LipschitzHilbert.Estimates.MartingaleMaximalL2
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

namespace OAI

/-! Actual integer-indexed dyadic line averages. The alternating grids are
handled directly, with no alignment premise between a packet and a root. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.DyadicLineGrid

theorem index_fiber (q k i : ℤ) : {x : ℝ | index q k x=i}=cell q k i := by
  ext x
  constructor
  · intro hx
    change index q k x=i at hx
    rw [←hx]
    exact mem_index_cell q k x
  · exact index_eq_of_mem

theorem index_measurable (q k : ℤ) : Measurable (index q k) := by
  apply measurable_to_countable'
  intro i
  change MeasurableSet {x : ℝ | index q k x=i}
  rw [index_fiber]
  exact cell_measurable q k i

theorem parent_index_eq (q k : ℤ) (x : ℝ) :
    parent q k (index q k x)=index q (k+1) x :=
  (index_eq_of_mem (cell_subset_parent q k (index q k x) (mem_index_cell q k x))).symm

def lineFiltration (q top : ℤ) : Filtration ℕ (inferInstance : MeasurableSpace ℝ) where
  seq n := MeasurableSpace.comap (index q (top-(n:ℤ))) inferInstance
  le' n := (index_measurable q (top-n)).comap_le
  mono' := monotone_nat_of_le_succ fun n => by
    have heq : index q (top-(n:ℤ)) =
        parent q (top-((n+1:ℕ):ℤ)) ∘ index q (top-((n+1:ℕ):ℤ)) := by
      funext x
      have h := parent_index_eq q (top-((n+1:ℕ):ℤ)) x
      have he : top-((n+1:ℕ):ℤ)+1=top-(n:ℤ) := by omega
      simpa only [Function.comp_apply,he] using h.symm
    rw [heq,←MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_of_countable _).comap_le

def rootMeasure (q top j : ℤ) : Measure ℝ := volume.restrict (cell q top j)

instance rootMeasure_finite (q top j : ℤ) : IsFiniteMeasure (rootMeasure q top j) := ⟨by
  change (volume.restrict (cell q top j)) univ < ∞
  rw [Measure.restrict_apply_univ]
  exact measure_Ico_lt_top⟩

def lineAverage (q top j : ℤ) (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (rootMeasure q top j)[f | lineFiltration q top n]

theorem lineAverage_martingale (q top j : ℤ) (f : ℝ → ℝ) :
    Martingale (lineAverage q top j f) (lineFiltration q top) (rootMeasure q top j) :=
  martingale_condExp f _ _

theorem lineAverage_memLp (q top j : ℤ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (rootMeasure q top j)) (n : ℕ) :
    MemLp (lineAverage q top j f n) 2 (rootMeasure q top j) := hf.condExp (by norm_num)

theorem lineAverage_constant (q top j : ℤ) (f : ℝ → ℝ) (n : ℕ) {x y : ℝ}
    (hxy : index q (top-(n:ℤ)) x=index q (top-(n:ℤ)) y) :
    lineAverage q top j f n x=lineAverage q top j f n y :=
  (show StronglyMeasurable[lineFiltration q top n] (lineAverage q top j f n) from
    stronglyMeasurable_condExp).factorsThrough hxy

/-- Each conditional expectation equals the literal average on the
actual dyadic cell containing the point. -/
theorem lineAverage_eq_cell_mean (q top j : ℤ) {f : ℝ → ℝ}
    (hf : Integrable f (rootMeasure q top j)) (n : ℕ) {x : ℝ}
    (hx : x∈cell q top j) :
    lineAverage q top j f n x =
      (∫ y in cell q (top-(n:ℤ)) (index q (top-(n:ℤ)) x), f y)/scale (top-(n:ℤ)) := by
  let s := cell q (top-(n:ℤ)) (index q (top-(n:ℤ)) x)
  have hsub : s⊆cell q top j := cell_subset_of_intersect (by omega)
    ⟨x,mem_index_cell q (top-(n:ℤ)) x,hx⟩
  have hs : MeasurableSet[lineFiltration q top n] s := by
    change MeasurableSet[lineFiltration q top n] (cell q (top-(n:ℤ)) (index q (top-(n:ℤ)) x))
    rw [←index_fiber]
    exact (comap_measurable (index q (top-(n:ℤ)))) (measurableSet_singleton _)
  have hs' : MeasurableSet s := cell_measurable _ _ _
  have hmass : (rootMeasure q top j).real s=scale (top-(n:ℤ)) := by
    rw [measureReal_def,rootMeasure,Measure.restrict_apply hs',inter_eq_left.mpr hsub]
    exact cell_length q (top-(n:ℤ)) (index q (top-(n:ℤ)) x)
  apply (eq_div_iff (scale_pos (top-(n:ℤ))).ne').mpr
  calc
    lineAverage q top j f n x*scale (top-(n:ℤ)) =
        ∫ y in s, lineAverage q top j f n x ∂rootMeasure q top j := by
      rw [setIntegral_const,smul_eq_mul,hmass,mul_comm]
    _ = ∫ y in s, lineAverage q top j f n y ∂rootMeasure q top j := by
      apply setIntegral_congr_fun hs'
      intro y hy
      exact lineAverage_constant q top j f n (index_eq_of_mem hy).symm
    _ = ∫ y in s, f y ∂rootMeasure q top j := setIntegral_condExp ((lineFiltration q top).le n) hf hs
    _ = ∫ y in s, f y := by
      rw [rootMeasure,Measure.restrict_restrict hs',inter_eq_left.mpr hsub]

/-- Doob's bound on a root has a constant independent of the root, grid,
and number of retained scales. -/
theorem lineAverage_maximal_energy (q top j : ℤ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (rootMeasure q top j)) (N : ℕ) :
    (∫ x, (finiteMaxSignal (lineAverage q top j f) N x)^2 ∂rootMeasure q top j) ≤
      4*∫ x, (f x)^2 ∂rootMeasure q top j := by
  have hmax := martingale_maximal_L2 (rootMeasure q top j) (lineFiltration q top)
    (lineAverage q top j f) (lineAverage_martingale q top j f)
    (fun n => lineAverage_memLp q top j hf n) N
  have hnorm : Integrable (fun x => ‖f x‖^(2:ℝ)) (rootMeasure q top j) := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using hf.integrable_sq
  have hcond := integral_norm_condExp_rpow_le (μ:=rootMeasure q top j)
    (m:=lineFiltration q top N) (p:=2) (by norm_num) hnorm
  have hcond' : (∫ x, (lineAverage q top j f N x)^2 ∂rootMeasure q top j) ≤
      ∫ x, (f x)^2 ∂rootMeasure q top j := by
    simpa only [lineAverage,Real.rpow_two,Real.norm_eq_abs,sq_abs] using hcond
  exact hmax.trans (mul_le_mul_of_nonneg_left hcond' (by norm_num))

end LipschitzHilbert.DyadicLineGrid

end

end OAI
