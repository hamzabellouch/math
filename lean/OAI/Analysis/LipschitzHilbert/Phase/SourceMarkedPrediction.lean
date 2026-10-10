import OAI.Analysis.LipschitzHilbert.Phase.SourceLocalPrediction
import OAI.Analysis.LipschitzHilbert.Trees.SourceMassStopping
import OAI.Analysis.LipschitzHilbert.Trees.SourceStoppedError

namespace OAI

/-! Marking belongs to an entire coarse line cell. On every unmarked
cell the prediction factor is exactly one. In particular a cell containing
an inactive point cannot contribute a marked factor. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace LipschitzHilbert.FiniteLineGrid
attribute [local instance] Classical.propDecidable

def markedValue (g : FiniteLineGrid) (coarse : ℕ) (marked : ℕ → Prop)
    (value : ℝ → ℝ) (x : ℝ) : ℝ :=
  if marked (g.index coarse x).val then value x else 1

def markedError (g : FiniteLineGrid) (coarse : ℕ) (marked : ℕ → Prop)
    (error : ℝ → ℝ) (x : ℝ) : ℝ :=
  if marked (g.index coarse x).val then error x else 0

theorem measurableSet_marked (g : FiniteLineGrid) (coarse : ℕ) (marked : ℕ → Prop) :
    MeasurableSet {x | marked (g.index coarse x).val} := by
  have hm := measurable_finite_profile (g.index coarse) (g.measurable_index_fiber coarse)
    (fun i => if marked i.val then (1:ℝ) else 0)
  convert hm (measurableSet_singleton (1:ℝ)) using 1
  ext x
  simp

theorem measurable_markedValue (g : FiniteLineGrid) (coarse : ℕ) (marked : ℕ → Prop)
    (value : ℝ → ℝ) (hvalue : Measurable value) : Measurable (g.markedValue coarse marked value) :=
  Measurable.ite (g.measurableSet_marked coarse marked) hvalue measurable_const

theorem measurable_markedError (g : FiniteLineGrid) (coarse : ℕ) (marked : ℕ → Prop)
    (error : ℝ → ℝ) (herror : Measurable error) : Measurable (g.markedError coarse marked error) :=
  Measurable.ite (g.measurableSet_marked coarse marked) herror measurable_const

/-- Only marked cells require an analytic predictor. The other cells
have factor one, retaining exact normalization and fine-cell constancy. -/
theorem exists_marked_source_prediction (g : FiniteLineGrid) (coarse fine : ℕ)
    (hcf : coarse ≤ fine) (hf : fine ≤ g.depth)
    (marked : ℕ → Prop) (good : Set ℝ) (beta error : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hF : ∀ i < g.branching^coarse, marked i → ∀ x, 0 ≤ F i x)
    (hint : ∀ i < g.branching^coarse, marked i →
      Integrable (F i) (intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
        ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)))
    (haverage : ∀ i < g.branching^coarse, marked i →
      (∫ x, F i x ∂intervalProbability (g.lineWindow coarse i (fine-coarse)).origin
        ((g.lineWindow coarse i (fine-coarse)).origin+(g.lineWindow coarse i (fine-coarse)).width)) ≤ 1)
    (hconstant : ∀ i < g.branching^coarse, marked i → ∀ x z,
      (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) x =
        (g.lineWindow coarse i (fine-coarse)).index (fine-coarse) z → F i x = F i z)
    (hcompare : ∀ i < g.branching^coarse, marked i →
      ∀ x ∈ g.cell coarse i ∩ good, beta x ≤ Real.exp (error x)*F i x) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧ (∀ x, 0 ≤ Γ x) ∧
      (∀ x z, g.index fine x = g.index fine z → Γ x = Γ z) ∧
      (∀ i : Fin (g.branching^g.depth),
        (∫ x in {x | g.index coarse x = i}, Γ x ∂volume.restrict g.root) ≤
          (volume.restrict g.root).real {x | g.index coarse x = i}) ∧
      (∀ x ∈ g.root, ¬marked (g.index coarse x).val → Γ x = 1) ∧
      ∀ x ∈ g.root ∩ good, g.markedValue coarse marked beta x ≤
        Real.exp (g.markedError coarse marked error x)*Γ x := by
  let F0 := fun i x => if marked i then F i x else 1
  have hpos (i : ℕ) (hi : i < g.branching^coarse) (x : ℝ)
      (_hx : x ∈ g.cell coarse i) : 0 ≤ F0 i x := by
    by_cases hm : marked i
    · simpa only [F0,ite_eq_left hm] using hF i hi hm x
    · simp only [F0,ite_eq_right hm]; norm_num
  have havg (i : ℕ) (hi : i < g.branching^coarse) :
      (∫ x in g.cell coarse i, F0 i x) ≤ volume.real (g.cell coarse i) := by
    by_cases hm : marked i
    · have ha := ((g.lineWindow coarse i (fine-coarse)).window_average_le (F i)
        (hint i hi hm) (haverage i hi hm)).2
      simpa only [F0,ite_eq_left hm,lineWindow_root] using ha
    · simp [F0,hm,integral_const,measureReal_def]
  obtain ⟨Γ,hmeas,hΓ,hconst,heq,hav⟩ := g.exists_patched_window_factor coarse fine hcf hf
    F0 hpos (by
      intro i hi x hx z hz hix
      by_cases hm : marked i
      · simp only [F0,ite_eq_left hm]
        apply hconstant i hi hm x z
        apply g.lineWindow_index_of_global coarse i (fine-coarse) (fine-coarse) hi le_rfl
          (by omega) hx hz
        simpa only [Nat.add_sub_of_le hcf] using hix
      · simp only [F0,ite_eq_right hm]) havg
  refine ⟨Γ,hmeas,hΓ,hconst,hav,?_,?_⟩
  · intro x hx hm
    rw [heq x hx]
    simp only [F0,ite_eq_right hm]
  · intro x hx
    have hi : (g.index coarse x).val < g.branching^coarse := by
      change g.rawIndex (min coarse g.depth) x < g.branching^coarse
      rw [Nat.min_eq_left (hcf.trans hf)]
      exact rawIndex_lt (g := {g with depth := coarse}) le_rfl x
    have hmem := (g.index_eq_iff_mem_cell (hcf.trans hf) hx.1 (g.index coarse x).val).mp rfl
    rw [heq x hx.1]
    by_cases hm : marked (g.index coarse x).val
    · simpa only [markedValue,markedError,F0,ite_eq_left hm] using
        hcompare _ hi hm x ⟨hmem,hx.2⟩
    · simp only [markedValue,markedError,F0,ite_eq_right hm,Real.exp_zero,one_mul,le_refl]

/-- The source's cellwise condition rules out marked factors as soon as
the actual point has crossed its mass cutoff. -/
theorem unmarked_of_mass_le (g : FiniteLineGrid) (coarse : ℕ) (marked : ℕ → Prop)
    (n : ℝ → ℝ) (M : ℝ)
    (hmark : ∀ i < g.branching^coarse, marked i → ∀ x ∈ g.cell coarse i, M < n x)
    (hcoarse : coarse ≤ g.depth) {x : ℝ} (hx : x ∈ g.root) (hn : n x ≤ M) :
    ¬marked (g.index coarse x).val := by
  intro hm
  have hi : (g.index coarse x).val < g.branching^coarse := by
    change g.rawIndex (min coarse g.depth) x < g.branching^coarse
    rw [Nat.min_eq_left hcoarse]
    exact rawIndex_lt (g := {g with depth := coarse}) le_rfl x
  exact (not_lt_of_ge hn) (hmark _ hi hm x ((g.index_eq_iff_mem_cell hcoarse hx _).mp rfl))

end LipschitzHilbert.FiniteLineGrid

namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

/-- Marked errors are a subfamily of the active forward mass-path errors.
No claim that pointwise stopping is itself a coarse-cell condition is used. -/
theorem eventually_source_marked_error (C A_M : ℝ) (hC : 0 ≤ C) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ (n e snapshot : ℕ → ℝ) (count : ℕ) (marked : ℕ → Prop),
    ∀ N : ℝ, 0 < N → Real.log N ≤ 2*L → n 0 ≤ L^C*N^2 →
      (∀ j, 0 ≤ n j) → Antitone n → n count ≤ L^A_M →
      (∀ j < count, marked j → L^A_M < n j) →
      (∀ j < count, marked j → snapshot j/2 ≤ pathDrop n j) →
      (∀ j < count, marked j → e j ≤ SourceParameters.step L^(-(1/32:ℝ))*snapshot j) →
      (∑ j ∈ Finset.range count, if marked j then e j else 0) ≤ 1 := by
  classical
  filter_upwards [eventually_source_snapshot_stopped_error C A_M hC hAM,
    eventually_ge_atTop (1:ℝ)] with L hL hlarge
  intro n e snapshot count marked N hN hlog hmass hn hanti hlast hmarked hdrop he
  let stop := firstMassStop n count (L^A_M)
  have hstop := firstMassStop_spec n count (L^A_M) hlast
  apply hL n (fun j => if marked j then e j else 0)
    (fun j => if marked j then snapshot j else 0) count stop hstop.1
    N hN hlog hmass hstop.2.2 (hn stop)
  · intro j hj
    by_cases hm : marked j
    · simpa only [ite_eq_left hm] using hdrop j (hj.trans_le hstop.1) hm
    · have hnj : 0 < n j :=
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hlarge) A_M).trans (hstop.2.2 j hj)
      simpa only [ite_eq_right hm,zero_div] using
        pathDrop_nonnegative n j hnj (hanti (Nat.le_succ j))
  · intro j hj
    by_cases hm : marked j
    · have hjstop : j < stop :=
        (firstMassStop_active_iff n count (L^A_M) hlast hanti j).mpr (hmarked j hj hm)
      simpa only [ite_eq_left hm,ite_eq_left hjstop] using he j hj hm
    · simp only [ite_eq_right hm,mul_zero,ite_self,le_refl]

end LipschitzHilbert

end

end OAI
