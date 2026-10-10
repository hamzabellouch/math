import Mathlib
import OAI.Probability.JammingConcavity.DeletionDeterministicRepairSmallness
import OAI.Probability.JammingConcavity.DeletionUniformGapCountFailureBound

namespace OAI

/-! Deletion Measure Preserving Select Rows. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
namespace MicroscopicJamming
abbrev SpinSpace (N : ℕ) := EuclideanSpace ℝ (Fin N)

def rowCount (α : ℝ) (N : ℕ) : ℕ := ⌊α * (N : ℝ)⌋₊

abbrev PatternMatrix (α : ℝ) (N : ℕ) :=
  Fin (rowCount α N) → Fin N → ℝ

 
def disorderLaw (ε α : ℝ) (N : ℕ) : Measure (PatternMatrix α N) :=
  Measure.pi fun _ => Measure.pi fun _ => coordinateLaw ε

 
def surfaceLaw (N : ℕ) : Measure (SpinSpace N) :=
  let σ := (volume : Measure (SpinSpace N)).toSphere
  Measure.map (fun y : Metric.sphere (0 : SpinSpace N) 1 =>
    Real.sqrt N • (y : SpinSpace N)) ((σ Set.univ)⁻¹ • σ)

def field {α : ℝ} {N : ℕ} (A : PatternMatrix α N)
    (x : SpinSpace N) (μ : Fin (rowCount α N)) : ℝ :=
  ∑ i, A μ i * (x i / Real.sqrt N)

def gap {α : ℝ} {N : ℕ} (A : PatternMatrix α N)
    (x : SpinSpace N) (μ : Fin (rowCount α N)) : ℝ :=
  1 + field A x μ

def potential (z : ℝ) : ℝ := (1 / 2 : ℝ) * (max (-1 - z) 0) ^ 2

def energy {α : ℝ} {N : ℕ} (A : PatternMatrix α N) (x : SpinSpace N) : ℝ :=
  ∑ μ, potential (field A x μ)

def satisfiable {α : ℝ} {N : ℕ} (A : PatternMatrix α N) : Prop :=
  ∃ x : SpinSpace N, ‖x‖ ^ 2 = (N : ℝ) ∧ energy A x = 0

def satProbability (ε α : ℝ) (N : ℕ) : ℝ :=
  ((disorderLaw ε α N) {A | satisfiable A}).toReal

 
def groundEnergy {α : ℝ} {N : ℕ} (A : PatternMatrix α N) : ℝ :=
  sInf (energy A '' {x : SpinSpace N | ‖x‖ ^ 2 = (N : ℝ)})

 
def unitEnergy {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j, potential (∑ i, A j i*y i)

def unitGround {m n : ℕ} (A : Fin m → Fin n → ℝ) : ℝ :=
  sInf (unitEnergy A '' Metric.sphere 0 1)

def unitSatisfiable {m n : ℕ} (A : Fin m → Fin n → ℝ) : Prop :=
  ∃ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 ∧ ∀ j, 0 ≤ 1+∑ i, A j i*y i

lemma potential_nonneg (z : ℝ) : 0 ≤ potential z := by
  unfold potential
  positivity

lemma potential_eq_zero_iff (z : ℝ) : potential z = 0 ↔ 0 ≤ 1+z := by
  rw [potential, mul_eq_zero]
  norm_num
  constructor <;> intro h <;> linarith

lemma unitEnergy_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ unitEnergy A y := by
  exact Finset.sum_nonneg (fun j _ => potential_nonneg _)

lemma unitEnergy_zero_iff {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    unitEnergy A y = 0 ↔ ∀ j, 0 ≤ 1+∑ i, A j i*y i := by
  rw [unitEnergy, Finset.sum_eq_zero_iff_of_nonneg (fun j _ => potential_nonneg _)]
  simp [potential_eq_zero_iff]

lemma continuous_unitEnergy {m n : ℕ} :
    Continuous (fun p : (Fin m → Fin n → ℝ) × EuclideanSpace ℝ (Fin n) =>
      unitEnergy p.1 p.2) := by
  unfold unitEnergy potential
  fun_prop

lemma continuous_unitGround {m n : ℕ} : Continuous (@unitGround m n) := by
  exact (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).continuous_sInf continuous_unitEnergy

lemma unitGround_attained {m n : ℕ} (hn : 0 < n) (A : Fin m → Fin n → ℝ) :
    ∃ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 ∧ unitGround A = unitEnergy A y ∧
      ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ = 1 → unitEnergy A y ≤ unitEnergy A z := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨y, hy, heq, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_sInf_image_eq_and_le (NormedSpace.sphere_nonempty.mpr (by norm_num))
      (continuous_unitEnergy.comp (continuous_const.prodMk continuous_id)).continuousOn
  refine ⟨y, by simpa using hy, heq, ?_⟩
  intro z hz
  exact hmin z (by simpa using hz)

lemma unitGround_nonneg {m n : ℕ} (hn : 0 < n) (A : Fin m → Fin n → ℝ) :
    0 ≤ unitGround A := by
  obtain ⟨y, _, h, _⟩ := unitGround_attained hn A
  rw [h]
  exact unitEnergy_nonneg A y

lemma unitGround_le {m n : ℕ} (hn : 0 < n) (A : Fin m → Fin n → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ = 1) : unitGround A ≤ unitEnergy A y := by
  obtain ⟨z, _, h, hmin⟩ := unitGround_attained hn A
  rw [h]
  exact hmin y hy

lemma unitSatisfiable_iff_ground {m n : ℕ} (hn : 0 < n) (A : Fin m → Fin n → ℝ) :
    unitSatisfiable A ↔ unitGround A = 0 := by
  constructor
  · rintro ⟨y, hy, hfeas⟩
    apply le_antisymm _ (unitGround_nonneg hn A)
    exact (unitGround_le hn A hy).trans_eq ((unitEnergy_zero_iff A y).mpr hfeas)
  · intro h
    obtain ⟨y, hy, heq, _⟩ := unitGround_attained hn A
    exact ⟨y, hy, (unitEnergy_zero_iff A y).mp (heq.symm.trans h)⟩

lemma measurableSet_unitSatisfiable {m n : ℕ} (hn : 0 < n) :
    MeasurableSet {A : Fin m → Fin n → ℝ | unitSatisfiable A} := by
  simp_rw [unitSatisfiable_iff_ground hn]
  exact (isClosed_eq continuous_unitGround continuous_const).measurableSet

lemma field_rescale {α : ℝ} {n : ℕ} (hn : 0 < n) (A : PatternMatrix α n)
    (y : SpinSpace n) (j : Fin (rowCount α n)) :
    field A (Real.sqrt n • y) j = ∑ i, A j i*y i := by
  have hs : Real.sqrt (n:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  simp [field, PiLp.smul_apply, smul_eq_mul, hs, mul_div_cancel_left₀]

lemma energy_rescale {α : ℝ} {n : ℕ} (hn : 0 < n) (A : PatternMatrix α n)
    (y : SpinSpace n) : energy A (Real.sqrt n • y) = unitEnergy A y := by
  simp [energy, unitEnergy, field_rescale hn]

lemma norm_rescale_sq {n : ℕ} {y : SpinSpace n} (hy : ‖y‖ = 1) :
    ‖Real.sqrt n • y‖^2 = (n:ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hy, mul_one,
    Real.sq_sqrt (Nat.cast_nonneg _)]

lemma exists_rescale_unit {n : ℕ} (hn : 0 < n) {x : SpinSpace n}
    (hx : ‖x‖^2 = (n:ℝ)) : ∃ y : SpinSpace n, ‖y‖ = 1 ∧ Real.sqrt n • y = x := by
  have hs : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hxnorm : ‖x‖ = Real.sqrt n := by
    rw [← hx, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨(Real.sqrt (n:ℝ))⁻¹ • x, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), hxnorm, inv_mul_cancel₀ hs.ne']
  · rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

lemma groundEnergy_eq_unitGround {α : ℝ} {n : ℕ} (hn : 0 < n) (A : PatternMatrix α n) :
    groundEnergy A = unitGround A := by
  unfold groundEnergy unitGround
  congr 1
  ext e
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := exists_rescale_unit hn hx
    exact ⟨y, by simpa using hy, (energy_rescale hn A y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Real.sqrt n • y, norm_rescale_sq (by simpa using hy), energy_rescale hn A y⟩

lemma satisfiable_iff_unit {α : ℝ} {n : ℕ} (hn : 0 < n) (A : PatternMatrix α n) :
    satisfiable A ↔ unitSatisfiable A := by
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨y, hy, rfl⟩ := exists_rescale_unit hn hx
    rw [energy_rescale hn] at he
    exact ⟨y, hy, (unitEnergy_zero_iff A y).mp he⟩
  · rintro ⟨y, hy, he⟩
    refine ⟨Real.sqrt n • y, norm_rescale_sq hy, ?_⟩
    rw [energy_rescale hn]
    exact (unitEnergy_zero_iff A y).mpr he

lemma coordinateLaw_memLp_two (ε : ℝ) : MemLp id 2 (coordinateLaw ε) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  exact ((memLp_id_gaussianReal (μ := 0) (v := Real.toNNReal (1-ε)) 2).integrable_sq.smul_measure (by norm_num)).add_measure
      ((memLp_id_gaussianReal (μ := 0) (v := Real.toNNReal (1+ε)) 2).integrable_sq.smul_measure (by norm_num))

lemma matrix_field_memLp_two {m n : ℕ} (ε : ℝ) (y : EuclideanSpace ℝ (Fin n))
    (j : Fin m) :
    MemLp (fun A : Fin m → Fin n → ℝ => ∑ i, A j i*y i) 2
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε) := by
  apply memLp_finsetSum
  intro i _
  have hh := (coordinateLaw_memLp_two ε).comp_measurePreserving
    ((measurePreserving_eval (fun _ : Fin n => coordinateLaw ε) i).comp
      (measurePreserving_eval (fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε) j))
  simpa [Function.comp_def, mul_comm] using hh.const_mul (y i)

lemma potential_le_quadratic (z : ℝ) : potential z ≤ 1+z^2 := by
  dsimp [potential]
  by_cases hz : 0 ≤ -1-z
  · rw [max_eq_left hz]
    nlinarith [sq_nonneg (z-1)]
  · rw [max_eq_right (by linarith)]
    nlinarith [sq_nonneg z]

lemma integrable_unitEnergy {m n : ℕ} (ε : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun A : Fin m → Fin n → ℝ => unitEnergy A y)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε) := by
  apply integrable_finsetSum
  intro j _
  apply (integrable_const (1:ℝ) |>.add (matrix_field_memLp_two ε y j).integrable_sq).mono'
  · apply Continuous.aestronglyMeasurable
    unfold potential
    fun_prop
  · filter_upwards [] with A
    rw [Real.norm_eq_abs, abs_of_nonneg (potential_nonneg _)]
    exact potential_le_quadratic _

lemma integrable_unitGround {m n : ℕ} (hn : 0 < n) (ε : ℝ) :
    Integrable (@unitGround m n)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => coordinateLaw ε) := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨y, hy⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin n)) (show (0:ℝ) ≤ 1 by norm_num)
  apply (integrable_unitEnergy ε y).mono' continuous_unitGround.aestronglyMeasurable
  filter_upwards [] with A
  rw [Real.norm_eq_abs, abs_of_nonneg (unitGround_nonneg hn A)]
  exact unitGround_le hn A hy

lemma integrable_groundEnergy {α : ℝ} {n : ℕ} (hn : 0 < n) (ε : ℝ) :
    Integrable (fun A : PatternMatrix α n => groundEnergy A) (disorderLaw ε α n) := by
  simpa only [groundEnergy_eq_unitGround hn, disorderLaw] using
    (integrable_unitGround (m := rowCount α n) hn ε)

end MicroscopicJamming

 

open Finset Set
open scoped BigOperators

namespace MicroscopicJamming

 

def finiteAverage {Ω : Type*} (P : Finset Ω) (f : Ω → ℝ) : ℝ :=
  (∑ ω ∈ P, f ω) / P.card

lemma finiteAverage_add {Ω : Type*} (P : Finset Ω) (f g : Ω → ℝ) :
    finiteAverage P (fun ω => f ω + g ω) = finiteAverage P f + finiteAverage P g := by
  simp [finiteAverage, Finset.sum_add_distrib, add_div]

lemma finiteAverage_sub {Ω : Type*} (P : Finset Ω) (f g : Ω → ℝ) :
    finiteAverage P (fun ω => f ω - g ω) = finiteAverage P f - finiteAverage P g := by
  simp [finiteAverage, Finset.sum_sub_distrib, sub_div]

lemma finiteAverage_mul_const {Ω : Type*} (P : Finset Ω) (f : Ω → ℝ) (c : ℝ) :
    finiteAverage P (fun ω => f ω*c) = finiteAverage P f*c := by
  unfold finiteAverage
  rw [← Finset.sum_mul]
  ring

lemma finiteAverage_const {Ω : Type*} {P : Finset Ω} (hP : P.Nonempty) (c : ℝ) :
    finiteAverage P (fun _ => c) = c := by
  simp [finiteAverage, (show (P.card:ℝ) ≠ 0 by exact_mod_cast hP.card_pos.ne'), mul_div_cancel_left₀]

lemma finiteAverage_sum {Ω ι : Type*} (P : Finset Ω) (S : Finset ι) (f : ι → Ω → ℝ) :
    finiteAverage P (fun ω => ∑ i ∈ S, f i ω) = ∑ i ∈ S, finiteAverage P (f i) := by
  simp only [finiteAverage, Finset.sum_div]
  rw [Finset.sum_comm]

lemma finiteAverage_congr {Ω : Type*} (P : Finset Ω) {f g : Ω → ℝ}
    (h : ∀ ω ∈ P, f ω = g ω) : finiteAverage P f = finiteAverage P g := by
  unfold finiteAverage
  congr 1
  exact Finset.sum_congr rfl h

lemma finiteAverage_mono {Ω : Type*} (P : Finset Ω) {f g : Ω → ℝ}
    (h : ∀ ω ∈ P, f ω ≤ g ω) : finiteAverage P f ≤ finiteAverage P g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

lemma finiteAverage_centered_product {Ω : Type*} {P : Finset Ω} (hP : P.Nonempty)
    (f g : Ω → ℝ) (p : ℝ) :
    finiteAverage P (fun ω => (f ω-p)*(g ω-p)) =
      finiteAverage P (fun ω => f ω*g ω) - finiteAverage P f*p - finiteAverage P g*p + p^2 := by
  calc
    _ = finiteAverage P (fun ω => ((f ω*g ω-f ω*p)-g ω*p)+p^2) :=
      finiteAverage_congr P (fun _ _ => by ring)
    _ = _ := by rw [finiteAverage_add, finiteAverage_sub, finiteAverage_sub,
      finiteAverage_mul_const, finiteAverage_mul_const, finiteAverage_const hP]

lemma finiteAverage_indicator {Ω : Type*} (P : Finset Ω) (s : Ω → Prop) [DecidablePred s] :
    finiteAverage P (fun ω => if s ω then 1 else 0) = ((P.filter s).card:ℝ)/P.card := by
  simp [finiteAverage]

 

lemma finite_indicator_variance {Ω ι : Type*} [DecidableEq ι]
    {P : Finset Ω} (hP : P.Nonempty) (S : Finset ι) (f : ι → Ω → ℝ) (p : ℝ)
    (hval : ∀ i ∈ S, ∀ ω ∈ P, f i ω = 0 ∨ f i ω = 1)
    (hmean : ∀ i ∈ S, finiteAverage P (f i) = p)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      finiteAverage P (fun ω => f i ω*f j ω) ≤ p^2) :
    finiteAverage P (fun ω => ((∑ i ∈ S, f i ω)-(S.card:ℝ)*p)^2) ≤ S.card/4 := by
  have hcent : ∀ i ∈ S, ∀ j ∈ S,
      finiteAverage P (fun ω => (f i ω-p)*(f j ω-p)) ≤
        if i = j then p*(1-p) else 0 := by
    intro i hi j hj
    rw [finiteAverage_centered_product hP, hmean i hi, hmean j hj]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      have hh : finiteAverage P (fun ω => f i ω*f i ω) = p := by
        rw [← hmean i hi]
        apply finiteAverage_congr
        intro ω hω
        rcases hval i hi ω hω with h | h <;> simp [h]
      rw [hh]
      exact le_of_eq (by ring)
    · rw [ite_eq_right hij]
      nlinarith [hpair i hi j hj hij]
  calc
    _ = finiteAverage P (fun ω => ∑ i ∈ S, ∑ j ∈ S, (f i ω-p)*(f j ω-p)) := by
      apply finiteAverage_congr
      intro ω _
      simp only [← Finset.sum_mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, sq]
    _ = ∑ i ∈ S, ∑ j ∈ S, finiteAverage P (fun ω => (f i ω-p)*(f j ω-p)) := by
      rw [finiteAverage_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact finiteAverage_sum P S _
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, if i = j then p*(1-p) else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum (hcent i hi)
    _ = (S.card:ℝ)*(p*(1-p)) := by simp
    _ ≤ S.card/4 := by
      have h := mul_le_mul_of_nonneg_left (show p*(1-p) ≤ 1/4 by nlinarith [sq_nonneg (p-1/2)])
        (Nat.cast_nonneg S.card : 0 ≤ (S.card:ℝ))
      nlinarith

 
lemma finite_chebyshev {Ω : Type*} {P : Finset Ω} (hP : P.Nonempty)
    (X : Ω → ℝ) (a t V : ℝ) (ht : 0 < t)
    (hV : finiteAverage P (fun ω => (X ω-a)^2) ≤ V) :
    finiteAverage P (fun ω => if a+t < X ω then 1 else 0) ≤ V/t^2 := by
  classical
  let Q := P.filter fun ω => a+t < X ω
  have hcard : (0:ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hsum : (Q.card:ℝ)*t^2 ≤ ∑ ω ∈ P, (X ω-a)^2 := by
    calc
      _ = ∑ _ω ∈ Q, t^2 := by simp
      _ ≤ ∑ ω ∈ Q, (X ω-a)^2 := by
        apply Finset.sum_le_sum
        intro ω hω
        have h := (Finset.mem_filter.mp hω).2
        nlinarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)
  have hh : ((Q.card:ℝ)/P.card)*t^2 ≤ V := by
    have hs := div_le_div_of_nonneg_right hsum hcard.le
    change (Q.card:ℝ)*t^2/(P.card:ℝ) ≤ finiteAverage P (fun ω => (X ω-a)^2) at hs
    calc
      _ = (Q.card:ℝ)*t^2/(P.card:ℝ) := by ring
      _ ≤ _ := hs.trans hV
  rw [finiteAverage_indicator]
  exact (le_div_iff₀ (sq_pos_of_pos ht)).mpr hh

 
def retainedSubsets (M m : ℕ) : Finset (Finset (Fin M)) := Finset.univ.powersetCard m

lemma retainedSubsets_nonempty {M m : ℕ} (hm : m ≤ M) : (retainedSubsets M m).Nonempty := by
  simpa [retainedSubsets] using (Finset.powersetCard_nonempty.mpr (by simpa using hm) :
    ((Finset.univ : Finset (Fin M)).powersetCard m).Nonempty)

lemma retainedSubsets_card (M m : ℕ) : (retainedSubsets M m).card = M.choose m := by
  simp [retainedSubsets]

lemma retained_single_count {M m : ℕ} (hm : 1 ≤ m) (i : Fin M) :
    ((retainedSubsets M m).filter fun I => i ∈ I).card = (M-1).choose (m-1) := by
  have h := Finset.card_filter_powersetCard_subset {i} (Finset.univ : Finset (Fin M)) m
    (Finset.subset_univ _) (by simpa using hm)
  simpa [retainedSubsets] using h

lemma retained_pair_count {M m : ℕ} (hm : 2 ≤ m) (i j : Fin M) (hij : i ≠ j) :
    ((retainedSubsets M m).filter fun I => i ∈ I ∧ j ∈ I).card = (M-2).choose (m-2) := by
  have h := Finset.card_filter_powersetCard_subset {i,j} (Finset.univ : Finset (Fin M)) m
    (Finset.subset_univ _) (by simpa [hij] using hm)
  simpa [retainedSubsets, hij, Finset.insert_subset_iff] using h

lemma choose_ratio_one {M m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ M) :
    ((M-1).choose (m-1):ℝ)/(M.choose m:ℝ) = (m:ℝ)/M := by
  have hM : 1 ≤ M := hm1.trans hmM
  have hc : (M.choose m:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmM).ne'
  have hMn : (M:ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have h := Nat.add_one_mul_choose_eq (M-1) (m-1)
  rw [Nat.sub_add_cancel hM, Nat.sub_add_cancel hm1] at h
  have hh : (M:ℝ)*((M-1).choose (m-1):ℝ) = (M.choose m:ℝ)*m := by exact_mod_cast h
  field_simp
  nlinarith

lemma choose_ratio_two {M m : ℕ} (hm2 : 2 ≤ m) (hmM : m ≤ M) :
    ((M-2).choose (m-2):ℝ)/(M.choose m:ℝ) =
      ((m:ℝ)/M)*((m-1:ℕ):ℝ)/(M-1:ℕ) := by
  have hm1 : 1 ≤ m := by omega
  have hM1 : 1 ≤ M := hm1.trans hmM
  have hmid : ((M-1).choose (m-1):ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.sub_le_sub_right hmM 1)).ne'
  have hfirst := choose_ratio_one hm1 hmM
  have hsecond := choose_ratio_one (M := M-1) (m := m-1) (by omega)
    (Nat.sub_le_sub_right hmM 1)
  rw [Nat.sub_sub, Nat.sub_sub] at hsecond
  norm_num only [Nat.reduceAdd] at hsecond
  calc
    _ = (((M-1).choose (m-1):ℝ)/(M.choose m:ℝ))*
      (((M-2).choose (m-2):ℝ)/((M-1).choose (m-1):ℝ)) := by
        field_simp
    _ = _ := by rw [hfirst, hsecond]; ring

lemma choose_ratio_two_le {M m : ℕ} (hm2 : 2 ≤ m) (hmM : m ≤ M) :
    ((M-2).choose (m-2):ℝ)/(M.choose m:ℝ) ≤ ((m:ℝ)/M)^2 := by
  have hM2 : 2 ≤ M := hm2.trans hmM
  have hM : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hMsub : (0:ℝ) < M-1 := by
    have : (2:ℝ) ≤ M := by exact_mod_cast hM2
    linarith
  rw [choose_ratio_two hm2 hmM, Nat.cast_sub (by omega : 1 ≤ m),
    Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
  have hfrac : ((m:ℝ)-1)/((M:ℝ)-1) ≤ (m:ℝ)/M := by
    apply (div_le_div_iff₀ hMsub hM).mpr
    have hh : (m:ℝ) ≤ M := by exact_mod_cast hmM
    nlinarith
  calc
    _ = ((m:ℝ)/M)*(((m:ℝ)-1)/((M:ℝ)-1)) := by ring
    _ ≤ ((m:ℝ)/M)*((m:ℝ)/M) := mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = _ := by ring

lemma retained_intersection_variance {M m : ℕ} (hm2 : 2 ≤ m) (hmM : m ≤ M)
    (S : Finset (Fin M)) :
    finiteAverage (retainedSubsets M m)
      (fun I => ((I ∩ S).card-(S.card:ℝ)*((m:ℝ)/M))^2) ≤ S.card/4 := by
  classical
  let f : Fin M → Finset (Fin M) → ℝ := fun i I => if i ∈ I then 1 else 0
  have h := finite_indicator_variance (retainedSubsets_nonempty hmM) S f ((m:ℝ)/M)
    (fun _ _ _ _ => by dsimp [f]; split_ifs <;> simp)
    (fun i _ => by
      dsimp [f]
      rw [finiteAverage_indicator, retained_single_count (by omega), retainedSubsets_card]
      exact choose_ratio_one (by omega) hmM)
    (fun i _ j _ hij => by
      have heq : (fun I => f i I*f j I) =
          (fun I => if i ∈ I ∧ j ∈ I then (1:ℝ) else 0) := by
        funext I
        dsimp [f]
        split_ifs <;> simp_all
      rw [heq, finiteAverage_indicator, retained_pair_count hm2 i j hij, retainedSubsets_card]
      exact choose_ratio_two_le hm2 hmM)
  have hs : ∀ I : Finset (Fin M), (∑ i ∈ S, f i I) = ((I ∩ S).card:ℝ) := by
    intro I
    simp [f, Finset.inter_comm]
  simpa only [hs] using h

 

theorem hypergeometric_deletion {M m N : ℕ} (hm2 : 2 ≤ m) (hmM : m ≤ M)
    (hN : 0 < N) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1/8)
    (hr : (m:ℝ) ≤ (1-8*ρ)*M) (S : Finset (Fin M))
    (hS : (S.card:ℝ) ≤ (1+ρ)*N) :
    finiteAverage (retainedSubsets M m)
      (fun I => if (1-2*ρ)*N < ((I ∩ S).card:ℝ) then 1 else 0) ≤
        (1+ρ)/(100*ρ^2*N) := by
  classical
  have hMr : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hrat : (m:ℝ)/M ≤ 1-8*ρ := (div_le_iff₀ hMr).mpr hr
  have hmean : (S.card:ℝ)*((m:ℝ)/M) ≤ (1-7*ρ)*N := by
    calc
      _ ≤ (S.card:ℝ)*(1-8*ρ) := mul_le_mul_of_nonneg_left hrat (Nat.cast_nonneg _)
      _ ≤ ((1+ρ)*N)*(1-8*ρ) := mul_le_mul_of_nonneg_right hS (by linarith)
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg ρ) hNr.le]
  have hv : finiteAverage (retainedSubsets M m)
      (fun I => (((I ∩ S).card:ℝ)-(S.card:ℝ)*((m:ℝ)/M))^2) ≤ (1+ρ)*N/4 :=
    (retained_intersection_variance hm2 hmM S).trans (by linarith)
  have ht : 0 < 5*ρ*N := by positivity
  have hcheb := finite_chebyshev (retainedSubsets_nonempty hmM)
    (fun I => ((I ∩ S).card:ℝ)) ((S.card:ℝ)*((m:ℝ)/M)) (5*ρ*N) ((1+ρ)*N/4) ht hv
  calc
    _ ≤ finiteAverage (retainedSubsets M m)
        (fun I => if (S.card:ℝ)*((m:ℝ)/M)+5*ρ*N < ((I ∩ S).card:ℝ) then 1 else 0) := by
      apply finiteAverage_mono
      intro I _
      split_ifs <;> norm_num at *
      nlinarith
    _ ≤ ((1+ρ)*N/4)/(5*ρ*N)^2 := hcheb
    _ = _ := by field_simp; ring

end MicroscopicJamming

namespace MicroscopicJamming
 

def selectRows {M m n : ℕ} (e : Fin m ↪ Fin M) (A : Fin M → Fin n → ℝ) :
    Fin m → Fin n → ℝ := fun j => A (e j)

lemma norm_select_le {M m : ℕ} (e : Fin m ↪ Fin M) (v : EuclideanSpace ℝ (Fin M)) :
    ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => v (e j))‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ j : Fin m, (v (e j))^2) ≤ ∑ j : Fin M, (v j)^2
  calc
    _ = ∑ j ∈ Finset.univ.map e, (v j)^2 := by simp
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

lemma matrixOperator_select_apply {M m n : ℕ} (e : Fin m ↪ Fin M)
    (A : Fin M → Fin n → ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    matrixOperator (selectRows e A) y =
      (EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => matrixOperator A y (e j)) := rfl

lemma matrixOperator_select_norm {M m n : ℕ} (e : Fin m ↪ Fin M)
    (A : Fin M → Fin n → ℝ) : ‖matrixOperator (selectRows e A)‖ ≤ ‖matrixOperator A‖ := by
  apply (matrixOperator (selectRows e A)).opNorm_le_bound (norm_nonneg _)
  intro y
  rw [matrixOperator_select_apply]
  exact (norm_select_le e (matrixOperator A y)).trans ((matrixOperator A).le_opNorm y)

lemma selected_rows_adjoint {M m n : ℕ} (e : Fin m ↪ Fin M)
    (A : Fin M → Fin n → ℝ) (T : Finset (Fin m)) (v : EuclideanSpace ℝ T) :
    (euclideanRows (matrixOperator (selectRows e A)) T).adjoint v =
      (matrixOperator A).adjoint (rowEmbedding (T.map e)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Finset.equivMap e T) v)) := by
  apply ext_inner_right ℝ
  intro y
  rw [LinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, rowEmbedding_inner]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Fintype.sum_equiv (Finset.equivMap e T)
  intro i
  change (∑ j, A (e i) j*y j)*v i =
    (∑ j, A (e i) j*y j)*v ((Finset.equivMap e T).symm ((Finset.equivMap e T) i))
  rw [Equiv.symm_apply_apply]

lemma selected_rows_lower_bound {M m n : ℕ} (e : Fin m ↪ Fin M)
    (A : Fin M → Fin n → ℝ) (ρ c : ℝ)
    (hA : ∀ T : Finset (Fin M), (T.card:ℝ) ≤ (1-ρ)*n →
      ∀ v : EuclideanSpace ℝ T,
        c*Real.sqrt n*‖v‖ ≤ ‖(matrixOperator A).adjoint (rowEmbedding T v)‖) :
    ∀ T : Finset (Fin m), (T.card:ℝ) ≤ (1-ρ)*n →
      ∀ v : EuclideanSpace ℝ T,
        c*Real.sqrt n*‖v‖ ≤ ‖(euclideanRows (matrixOperator (selectRows e A)) T).adjoint v‖ := by
  intro T hT v
  rw [selected_rows_adjoint]
  have h := hA (T.map e) (by simpa using hT)
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Finset.equivMap e T) v)
  simpa only [LinearIsometryEquiv.norm_map] using h

 
lemma measurePreserving_selectRows {M m n : ℕ} (e : Fin m ↪ Fin M)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    MeasurePreserving (selectRows (n := n) e)
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin n => ν)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => ν) := by
  let μ := Measure.pi fun _ : Fin n => ν
  have hi : iIndepFun (fun j : Fin M => Function.eval j)
      (Measure.pi fun _ : Fin M => μ) :=
    iIndepFun_pi (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)
  have hj := iIndepFun.precomp e.injective hi
  refine ⟨by unfold selectRows; fun_prop, ?_⟩
  change (Measure.pi fun _ : Fin M => μ).map (fun A j => A (e j)) = _
  rw [hj.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)]
  congr 1
  funext j
  exact (measurePreserving_eval (fun _ : Fin M => μ) (e j)).map_eq

end MicroscopicJamming

end

end OAI
