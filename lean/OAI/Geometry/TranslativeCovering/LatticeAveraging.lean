import OAI.Geometry.CoveringDensity.Model

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace LatticeAveraging
open Set MeasureTheory
open scoped ENNReal BigOperators Pointwise
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def field {n : ℕ} {I : Type u_1} [Fintype I]
    (Λ : Submodule ℤ (Space n)) (p : I → Space n) (f : Space n → ℝ≥0∞) (y : Space n) : ℝ≥0∞ :=
  ∑ i,∑' l : Λ,f (y-p i-l.val)

lemma measurable_field {n : ℕ} {I : Type u_2} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    (p : I → Space n) {f : Space n → ℝ≥0∞} (hf : Measurable f) :
    Measurable (field Λ p f) := by
  let : Countable Λ := countable_of_Lindelof_of_discrete
  apply Finset.measurable_sum
  intro i _
  exact Measurable.tsum fun l => hf.comp ((measurable_id.sub_const _).sub_const _)

lemma one_coset {n : ℕ} (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (p : Space n) {f : Space n → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in F,∑' l : Λ,f (y-p-l.val) = ∫⁻ x,f x := by
  let : Countable Λ := countable_of_Lindelof_of_discrete
  rw [lintegral_tsum (f := fun l : Λ => fun y => f (y-p-l.val))
    (fun l => (hf.comp ((measurable_id.sub_const p).sub_const l.val)).aemeasurable)]
  let : VAddInvariantMeasure Λ (Space n) volume :=
    inferInstanceAs (VAddInvariantMeasure Λ.toAddSubgroup (Space n) volume)
  have heq := hF.lintegral_eq_tsum' (fun x => f (x-p))
  rw [lintegral_sub_right_eq_self] at heq
  apply Eq.trans _ heq.symm
  apply tsum_congr
  intro l
  congr 1
  funext y
  congr 1
  change y-p-l.val = -l.val+y-p
  abel

lemma averaging {n : ℕ} {I : Type u_3} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (p : I → Space n) {f : Space n → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in F,field Λ p f y = (Fintype.card I:ℝ≥0∞)*∫⁻ x,f x := by
  let : Countable Λ := countable_of_Lindelof_of_discrete
  unfold field
  rw [lintegral_finsetSum (f := fun i : I => fun y => ∑' l : Λ, f (y-p i-l.val))
    Finset.univ (fun i _ => Measurable.tsum
    fun l => hf.comp ((measurable_id.sub_const (p i)).sub_const l.val))]
  simp_rw [one_coset Λ hF _ hf]
  simp

lemma periodic {n : ℕ} {I : Type u_4} [Fintype I]
    (Λ : Submodule ℤ (Space n)) (p : I → Space n) (f : Space n → ℝ≥0∞)
    (y : Space n) (l : Λ) : field Λ p f (y+l.val) = field Λ p f y := by
  unfold field
  apply Finset.sum_congr rfl
  intro i _
  have hh := (Equiv.addRight l).tsum_eq (fun k : Λ => f (y+l.val-p i-k.val))
  change (∑' k : Λ, f (y+l.val-p i-(k.val+l.val))) = _ at hh
  simpa only [show ∀ k : Λ,
    y+l.val-p i-(k.val+l.val) = y-p i-k.val by intro k; abel] using hh.symm

noncomputable def uniformWindow {n : ℕ} (F : Set (Space n)) : Measure (Space n) :=
  (volume F)⁻¹ • volume.restrict F

lemma normalized_averaging {n : ℕ} {I : Type u_5} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (p : I → Space n) {f : Space n → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y,field Λ p f y ∂uniformWindow F =
      ((Fintype.card I:ℝ≥0∞)/volume F)*∫⁻ x,f x := by
  rw [uniformWindow,lintegral_smul_measure,averaging Λ hF p hf]
  simp only [div_eq_mul_inv]
  ac_rfl

lemma probability_window {n : ℕ} {F : Set (Space n)}
    (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞) :
    IsProbabilityMeasure (uniformWindow F) := by
  constructor
  rw [uniformWindow,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hF0 hFtop

lemma count_integral {n : ℕ} {I : Type u_6} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (p : I → Space n) {B : Set (Space n)} (hB : MeasurableSet B) :
    ∫⁻ y in F,field Λ p (B.indicator (fun _ => 1)) y = (Fintype.card I:ℝ≥0∞)*volume B := by
  rw [averaging Λ hF p (measurable_const.indicator hB),lintegral_indicator hB]
  simp

lemma covolume_intensity {n : ℕ} {I : Type u_7} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume) :
    ((Fintype.card I:ℝ≥0∞)/volume F).toReal = (Fintype.card I:ℝ)/ZLattice.covolume Λ volume := by
  rw [ENNReal.toReal_div,ENNReal.toReal_natCast,ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hF]
  rfl

end LatticeAveraging

end OAI
