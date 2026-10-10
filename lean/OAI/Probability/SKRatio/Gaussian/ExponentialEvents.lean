import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKRatioClock.Regression

def ExponentialEmpiricalConcentration {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (ρ : ∀ n, Measure (H n)) (X : ∀ n, H n → Fin n → E) (ν : Measure E) : Prop :=
  ∀ (f : E → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ B : ℝ,
    (∀ x, |f x| ≤ B) → ∀ ε : ℝ, 0 < ε →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n in atTop,
      ρ n {h | ε ≤ |(∑ i, f (X n h i))/(n:ℝ) - ∫ x, f x ∂ν|} ≤
        ENNReal.ofReal (C * Real.exp (-c*(n:ℝ)))

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

lemma ExponentiallyRare.without_prefactor {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {A : ∀ n, Set (H n)} (hA : ExponentiallyRare ρ A) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n in atTop, ρ n (A n) ≤ ENNReal.ofReal (Real.exp (-c*n)) := by
  obtain ⟨C,c,hC,hc,he⟩ := hA
  refine ⟨c/2,by positivity,?_⟩
  have hnc := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  filter_upwards [he,hnc.eventually (eventually_ge_atTop (2*Real.log C/c))] with n hn hsize
  apply hn.trans
  apply ENNReal.ofReal_le_ofReal
  rw [show C*Real.exp (-c*n)=Real.exp (Real.log C-c*n) by
    rw [Real.exp_sub,Real.exp_log hC,neg_mul,Real.exp_neg,div_eq_mul_inv] ]
  apply Real.exp_le_exp.mpr
  have hh := (div_le_iff₀ hc).mp hsize
  nlinarith

end SKRatioClock.Regression

end
end

end OAI
