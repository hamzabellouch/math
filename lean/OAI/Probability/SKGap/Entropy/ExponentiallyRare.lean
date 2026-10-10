import Mathlib
import OAI.Probability.SKGap.Entropy.ExponentialEmpiricalConcentration

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
namespace SKGapCutoff.Regression

def ExponentiallyRare {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (A : ∀ n, Set (H n)) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n in atTop,
    ρ n (A n) ≤ ENNReal.ofReal (C * Real.exp (-c*(n:ℝ)))

lemma ExponentiallyRare.mono {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {A B : ∀ n, Set (H n)}
    (hB : ExponentiallyRare ρ B) (hAB : ∀ᶠ n in atTop, A n ⊆ B n) :
    ExponentiallyRare ρ A := by
  obtain ⟨C,c,hC,hc,he⟩ := hB
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [he,hAB] with n hn hABn
  exact (measure_mono hABn).trans hn

lemma ExponentiallyRare.union {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {A B : ∀ n, Set (H n)}
    (hA : ExponentiallyRare ρ A) (hB : ExponentiallyRare ρ B) :
    ExponentiallyRare ρ (fun n => A n ∪ B n) := by
  obtain ⟨C,c,hC,hc,he⟩ := hA
  obtain ⟨D,d,hD,hd,hf⟩ := hB
  refine ⟨C+D,min c d,add_pos hC hD,lt_min hc hd,?_⟩
  filter_upwards [he,hf] with n hn hm
  refine (measure_union_le _ _).trans ((add_le_add hn hm).trans ?_)
  have hc' : Real.exp (-c*(n:ℝ)) ≤ Real.exp (-min c d*(n:ℝ)) :=
    Real.exp_le_exp.mpr (by
      have := min_le_left c d
      nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hd' : Real.exp (-d*(n:ℝ)) ≤ Real.exp (-min c d*(n:ℝ)) :=
    Real.exp_le_exp.mpr (by
      have := min_le_right c d
      nlinarith [Nat.cast_nonneg (α := ℝ) n])
  rw [add_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hc' hC.le))
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hd' hD.le))

lemma exponentiallyRare_empty {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) : ExponentiallyRare ρ (fun _ => ∅) := by
  refine ⟨1,1,by norm_num,by norm_num,Filter.Eventually.of_forall ?_⟩
  intro n
  simp only [measure_empty, zero_le]

lemma ExponentiallyRare.iUnion_finite {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {ι : Type*} [Finite ι]
    {A : ι → ∀ n, Set (H n)} (hA : ∀ i, ExponentiallyRare ρ (A i)) :
    ExponentiallyRare ρ (fun n => ⋃ i, A i n) := by
  classical
  cases nonempty_fintype ι
  have hs (s : Finset ι) : ExponentiallyRare ρ (fun n => ⋃ i ∈ s, A i n) := by
    induction s using Finset.induction_on with
    | empty => simpa using exponentiallyRare_empty ρ
    | @insert i s hi ih =>
      have heq : (fun n => ⋃ j ∈ insert i s, A j n) =
          (fun n => A i n ∪ ⋃ j ∈ s, A j n) := by
        funext n
        ext h
        simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
        aesop
      rw [heq]
      exact (hA i).union ih
  simpa using hs Finset.univ

def ExponentialConvergence {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) {E : Type*} [PseudoMetricSpace E]
    (X : ∀ n, H n → E) (x : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ExponentiallyRare ρ (fun n => {h | ε ≤ dist (X n h) x})

lemma ExponentialConvergence.continuous_map
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {X : ∀ n, H n → E} {x : E} (hX : ExponentialConvergence ρ X x)
    {f : E → F} (hf : ContinuousAt f x) :
    ExponentialConvergence ρ (fun n h => f (X n h)) (f x) := by
  intro ε hε
  obtain ⟨δ,hδ,hδe⟩ := Metric.continuousAt_iff.mp hf ε hε
  apply (hX δ hδ).mono
  refine Filter.Eventually.of_forall ?_
  intro n h hh
  by_contra hnot
  have hnear : dist (X n h) x < δ := lt_of_not_ge hnot
  exact (not_lt_of_ge hh) (hδe hnear)

lemma ExponentialConvergence.prod
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {X : ∀ n, H n → E} {Y : ∀ n, H n → F} {x : E} {y : F}
    (hX : ExponentialConvergence ρ X x) (hY : ExponentialConvergence ρ Y y) :
    ExponentialConvergence ρ (fun n h => (X n h,Y n h)) (x,y) := by
  intro ε hε
  apply ((hX ε hε).union (hY ε hε)).mono
  exact Filter.Eventually.of_forall (fun n h hh => by
    simpa only [Prod.dist_eq, le_max_iff, Set.mem_union, Set.mem_ofPred_eq] using hh)

lemma ExponentialConvergence.pi_finite
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, PseudoMetricSpace (E i)]
    {X : ∀ n, H n → ∀ i, E i} {x : ∀ i, E i}
    (hX : ∀ i, ExponentialConvergence ρ (fun n h => X n h i) (x i)) :
    ExponentialConvergence ρ X x := by
  intro ε hε
  apply (ExponentiallyRare.iUnion_finite (fun i => hX i ε hε)).mono
  refine Filter.Eventually.of_forall ?_
  intro n h hh
  by_contra hn
  have hall : ∀ i, dist (X n h i) (x i) < ε := by
    intro i
    apply lt_of_not_ge
    intro hi
    exact hn (Set.mem_iUnion.mpr ⟨i,hi⟩)
  exact (not_lt_of_ge hh) ((dist_pi_lt_iff hε).mpr hall)

lemma ExponentialEmpiricalConcentration.average
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    ExponentialConvergence ρ (fun n h => (∑ i, f (X n h i))/(n:ℝ)) (∫ x, f x ∂ν) := by
  intro ε hε
  simpa only [ExponentiallyRare, Real.dist_eq] using hX f K hf B hB ε hε

lemma ExponentialEmpiricalConcentration.map
    {E F : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (g : E → F) {L : ℝ≥0} (hg : LipschitzWith L g) :
    ExponentialEmpiricalConcentration ρ (fun n h i => g (X n h i)) (ν.map g) := by
  intro f K hf B hB ε hε
  have hh := hX (f ∘ g) (K*L) (hf.comp hg) B (fun x => hB (g x)) ε hε
  have hm : ∫ y, f y ∂ν.map g = ∫ x, f (g x) ∂ν :=
    integral_map hg.continuous.measurable.aemeasurable hf.continuous.measurable.aestronglyMeasurable
  simpa only [Function.comp_apply, hm] using hh

theorem ExponentialEmpiricalConcentration.parameter_map
    {E F A : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F] [PseudoMetricSpace A]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (C : ∀ n, H n → A) (c : A) (hC : ExponentialConvergence ρ C c)
    (g : A → E → F) {L : ℝ≥0} (hg : LipschitzWith L (g c))
    (M : ℝ) (hM : 0 ≤ M) (hgc : ∀ a x, dist (g a x) (g c x) ≤ M*dist a c) :
    ExponentialEmpiricalConcentration ρ (fun n h i => g (C n h) (X n h i))
      (ν.map (g c)) := by
  have hxmap := hX.map (g c) hg
  intro f K hf B hB ε hε
  have hs : ExponentiallyRare ρ (fun n => {h | ε/2 ≤
      |(∑ i, f (g c (X n h i)))/(n:ℝ) - ∫ x, f x ∂ν.map (g c)|}) :=
    hxmap f K hf B hB (ε/2) (by positivity)
  let δ := ε/(2*((K:ℝ)*M+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcrare := hC δ hδ
  apply (hs.union hcrare).mono
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro h hh
  by_cases hb : ε/2 ≤ |(∑ i, f (g c (X n h i)))/(n:ℝ) - ∫ x, f x ∂ν.map (g c)|
  · exact Or.inl hb
  apply Or.inr
  by_contra hcnot
  have hcclose : dist (C n h) c < δ := lt_of_not_ge hcnot
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hdiff : |(∑ i, f (g (C n h) (X n h i)))/(n:ℝ) -
      (∑ i, f (g c (X n h i)))/(n:ℝ)| ≤ (K:ℝ)*M*dist (C n h) c := by
    rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hnR]
    apply (div_le_iff₀ hnR).mpr
    calc
      |∑ i, (f (g (C n h) (X n h i))-f (g c (X n h i)))| ≤
          ∑ i, |f (g (C n h) (X n h i))-f (g c (X n h i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (K:ℝ)*M*dist (C n h) c := by
        gcongr with i
        exact (hf.dist_le_mul _ _).trans
          (by calc
            (K:ℝ)*dist (g (C n h) (X n h i)) (g c (X n h i)) ≤
                (K:ℝ)*(M*dist (C n h) c) := mul_le_mul_of_nonneg_left (hgc _ _) K.coe_nonneg
            _ = (K:ℝ)*M*dist (C n h) c := by ring)
      _ = (K:ℝ)*M*dist (C n h) c*(n:ℝ) := by simp [mul_comm]
  have hδbound : (K:ℝ)*M*δ ≤ ε/2 := by
    dsimp [δ]
    have hp : 0 < 2*((K:ℝ)*M+1) := by positivity
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    field_simp
    nlinarith [mul_nonneg K.coe_nonneg hM]
  have hstep : (K:ℝ)*M*dist (C n h) c ≤ ε/2 :=
    (mul_le_mul_of_nonneg_left hcclose.le (mul_nonneg K.coe_nonneg hM)).trans hδbound
  have ht := abs_add_le
    ((∑ i, f (g (C n h) (X n h i)))/(n:ℝ) - (∑ i, f (g c (X n h i)))/(n:ℝ))
    ((∑ i, f (g c (X n h i)))/(n:ℝ) - ∫ x, f x ∂ν.map (g c))
  rw [sub_add_sub_cancel] at ht
  have hb' := lt_of_not_ge hb
  exact (not_lt_of_ge hh) (ht.trans_lt (by linarith))

lemma bounded_product_lipschitz {E : Type*} [PseudoMetricSpace E]
    {f g : E → ℝ} {K L B D : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hb : ∀ x, |f x| ≤ B) (hd : ∀ x, |g x| ≤ D) :
    LipschitzWith (K*D+L*B) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hid : f x*g x-f y*g y = (f x-f y)*g x + f y*(g x-g y) := by ring
  rw [hid]
  calc
    |(f x-f y)*g x+f y*(g x-g y)| ≤ |(f x-f y)*g x|+|f y*(g x-g y)| := abs_add_le _ _
    _ = |f x-f y| * |g x|+|f y| * |g x-g y| := by rw [abs_mul, abs_mul]
    _ ≤ ((K:ℝ)*dist x y)*(D:ℝ)+(B:ℝ)*((L:ℝ)*dist x y) := by
      gcongr
      · exact hf.dist_le_mul x y
      · exact hd x
      · exact hb y
      · exact hg.dist_le_mul x y
    _ = ((K*D+L*B:ℝ≥0):ℝ)*dist x y := by push_cast; ring

lemma ExponentialEmpiricalConcentration.gram
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {K B : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hB : ∀ i x, |f i x| ≤ B) :
    ExponentialConvergence ρ
      (fun n h i j => (∑ a, f i (X n h a)*f j (X n h a))/(n:ℝ))
      (fun i j => ∫ x, f i x*f j x ∂ν) := by
  apply ExponentialConvergence.pi_finite
  intro i
  apply ExponentialConvergence.pi_finite
  intro j
  apply hX.average (fun x => f i x*f j x)
    (bounded_product_lipschitz (hf i) (hf j) (hB i) (hB j)) ((B:ℝ)^2)
  intro x
  rw [abs_mul, pow_two]
  exact mul_le_mul (hB i x) (hB j x) (abs_nonneg _) B.coe_nonneg

lemma ExponentialConvergence.matrix_inv
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ∀ n, H n → ι → ι → ℝ} {a : ι → ι → ℝ}
    (hA : ExponentialConvergence ρ A a) (ha : Matrix.det a ≠ 0) :
    ExponentialConvergence ρ (fun n h i j => ((show Matrix ι ι ℝ from A n h)⁻¹) i j)
      (fun i j => ((show Matrix ι ι ℝ from a)⁻¹) i j) := by
  apply hA.continuous_map (f := fun a : ι → ι → ℝ => (fun i j => ((show Matrix ι ι ℝ from a)⁻¹) i j))
  apply continuousAt_matrix_inv
  simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ ha)

lemma ExponentialConvergence.matrix_mulVec
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : ∀ n, H n → ι → κ → ℝ} {a : ι → κ → ℝ}
    {B : ∀ n, H n → κ → ℝ} {b : κ → ℝ}
    (hA : ExponentialConvergence ρ A a) (hB : ExponentialConvergence ρ B b) :
    ExponentialConvergence ρ (fun n h => (A n h) *ᵥ (B n h)) (a *ᵥ b) := by
  exact (hA.prod hB).continuous_map (f := fun z => z.1 *ᵥ z.2)
    (continuous_fst.matrix_mulVec continuous_snd).continuousAt

theorem ExponentialEmpiricalConcentration.projection_coefficients
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → E → ℝ) (g : E → ℝ) {K B : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hg : LipschitzWith K g)
    (hB : ∀ i x, |f i x| ≤ B) (hBg : ∀ x, |g x| ≤ B)
    (hdet : Matrix.det (fun i j => ∫ x, f i x*f j x ∂ν) ≠ 0) :
    ExponentialConvergence ρ
      (fun n h => (show Matrix ι ι ℝ from fun i j => (∑ a, f i (X n h a)*f j (X n h a))/(n:ℝ))⁻¹ *ᵥ
        (fun i => (∑ a, f i (X n h a)*g (X n h a))/(n:ℝ)))
      ((show Matrix ι ι ℝ from fun i j => ∫ x, f i x*f j x ∂ν)⁻¹ *ᵥ
        (fun i => ∫ x, f i x*g x ∂ν)) := by
  apply ((hX.gram f hf hB).matrix_inv hdet).matrix_mulVec
  apply ExponentialConvergence.pi_finite
  intro i
  apply hX.average (fun x => f i x*g x)
    (bounded_product_lipschitz (hf i) hg (hB i) hBg) ((B:ℝ)^2)
  intro x
  rw [abs_mul, pow_two]
  exact mul_le_mul (hB i x) (hBg x) (abs_nonneg _) B.coe_nonneg

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology

end

end OAI
