import OAI.Analysis.LipschitzHilbert.Trees.SourceGlobalDyadicMaximal

namespace OAI

/-! Weak L1 bounds for actual finite dyadic line averages. The constants
are independent of the root, depth, and cell length. These supply the
one-dimensional part of the auxiliary covering maximal operator. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.DyadicLineGrid

theorem lineAverage_maximal_weak_L1 (q top j : ℤ) {f : ℝ → ℝ}
    (_hf : Integrable f (rootMeasure q top j)) (N : ℕ) (t : ℝ) (ht : 0<t) :
    (rootMeasure q top j).real {x | t ≤ finiteMaxSignal (lineAverage q top j f) N x} ≤
      t⁻¹*(∫ x, |f x| ∂rootMeasure q top j) := by
  have hmax := martingale_maximal_L1 (lineAverage_martingale q top j f) ht N
  have he : {x | ∃ i ≤ N, t ≤ |lineAverage q top j f i x|}=
      {x | t ≤ finiteMaxSignal (lineAverage q top j f) N x} := by
    ext x
    simp only [finiteMaxSignal,mem_ofPred_eq,Finset.le_sup'_iff,Finset.mem_range,Nat.lt_succ_iff]
  rw [he] at hmax
  exact hmax.trans (mul_le_mul_of_nonneg_left
    (integral_abs_condExp_le (μ:=rootMeasure q top j) (m:=lineFiltration q top N) f)
      (inv_nonneg.mpr ht.le))

theorem dyadicMaximal_root_weak_L1 (q top j : ℤ) {f : ℝ → ℝ}
    (hf : Integrable f (rootMeasure q top j)) (N : ℕ) (t : ℝ) (ht : 0<t) :
    (rootMeasure q top j).real {x | t ≤ dyadicMaximal q top N f x} ≤
      t⁻¹*(∫ x, |f x| ∂rootMeasure q top j) := by
  have he : (rootMeasure q top j) {x | t ≤ dyadicMaximal q top N f x}=
      (rootMeasure q top j) {x | t ≤ finiteMaxSignal (lineAverage q top j f) N x} := by
    apply measure_congr
    change ∀ᵐ x ∂volume.restrict (cell q top j), _
    filter_upwards [ae_restrict_mem (cell_measurable q top j)] with x hx
    simp only [dyadicMaximal_eq_on_root q top j N hf hx]
  rw [measureReal_def,he,←measureReal_def]
  exact lineAverage_maximal_weak_L1 q top j hf N t ht

theorem dyadicMaximal_weak_L1 (q top : ℤ) {f : ℝ → ℝ} (hf : Integrable f volume)
    (N : ℕ) (t : ℝ) (ht : 0<t) :
    volume {x | t ≤ dyadicMaximal q top N f x} ≤ ENNReal.ofReal (t⁻¹*(∫ x, |f x|)) := by
  let E := {x | t ≤ dyadicMaximal q top N f x}
  have hE : MeasurableSet E := measurableSet_le measurable_const (dyadicMaximal_measurable q top N f)
  let u := E.indicator (fun _ => (1:ℝ))
  have hu0 : ∀ x, 0 ≤ u x := by
    intro x
    by_cases hx : x∈E <;> simp [u,hx]
  have hcover : ⋃ j : ℤ, cell q top j=(univ:Set ℝ) := by
    apply Set.eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨index q top x,mem_index_cell q top x⟩
  have hdisj : Pairwise (fun i j : ℤ => Disjoint (cell q top i) (cell q top j)) :=
    fun _ _ h => cells_disjoint q top h
  have hui (j : ℤ) : IntegrableOn u (cell q top j) volume := by
    exact (integrable_const (1:ℝ) (μ:=rootMeasure q top j)).indicator hE
  have hbound (j : ℤ) : (∫ x in cell q top j, u x) ≤ t⁻¹*(∫ x in cell q top j, |f x|) := by
    have hh := dyadicMaximal_root_weak_L1 q top j hf.integrableOn N t ht
    change (∫ x, u x ∂rootMeasure q top j) ≤ _
    simpa only [u,integral_indicator_const (1:ℝ) hE,smul_eq_mul,mul_one,E,rootMeasure] using hh
  obtain ⟨hui,huint⟩ := integral_le_of_partition volume (cell q top) (cell_measurable q top)
    hdisj hcover u (fun x => |f x|) hu0 hf.abs hui hbound
  have hfinite : volume E≠∞ := by
    have h := (integrableOn_const_iff (C:=(1:ℝ))).mp ((integrable_indicator_iff hE).mp hui)
    have hh : volume E<∞ := by simpa using h
    exact hh.ne
  have hreal : (volume E).toReal ≤ t⁻¹*(∫ x, |f x|) := by
    simpa only [u,integral_indicator_const (1:ℝ) hE,smul_eq_mul,mul_one,measureReal_def] using huint
  rw [←ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hreal

end LipschitzHilbert.DyadicLineGrid

end

end OAI
