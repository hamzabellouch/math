import Mathlib
import OAI.Probability.Perceptron.Variational.IndexedGaussianMarks

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

def indexedVertexDepth : (n : ℕ) → IndexedVertex n → Fin n
  | 0,v => v.elim
  | n+1,v => match v.2.2 with
    | .inl _ => 0
    | .inr w => (indexedVertexDepth n w).succ

lemma indexedLeafVertex_depth (n : ℕ) (l : IndexedLeaf n) (i : Fin n) :
    indexedVertexDepth n (indexedLeafVertex n l i) = i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => simpa only [indexedLeafVertex,Fin.cases_succ,indexedVertexDepth] using congrArg Fin.succ (ih l.2.2 i)

def indexedSharedVertexDepth (n : ℕ) : SharedVertex n → Fin (n+1)
  | .inl _ => 0
  | .inr v => (indexedVertexDepth n v).succ

lemma indexedLeafSharedVertex_depth (n : ℕ) (l : IndexedLeaf n) (i : Fin (n+1)) :
    indexedSharedVertexDepth n (indexedLeafSharedVertex n l i) = i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => simpa only [indexedLeafSharedVertex,Fin.cases_succ,indexedSharedVertexDepth] using
      congrArg Fin.succ (indexedLeafVertex_depth n l i)

def indexedCommonDepth : (n : ℕ) → IndexedLeaf n → IndexedLeaf n → Fin (n+1)
  | 0,_,_ => 0
  | n+1,l,m => if l.1=m.1 ∧ l.2.1=m.2.1 then (indexedCommonDepth n l.2.2 m.2.2).succ else 0

lemma indexedCommonDepth_comm (n : ℕ) (l m : IndexedLeaf n) :
    indexedCommonDepth n l m = indexedCommonDepth n m l := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [indexedCommonDepth,ih m.2.2 l.2.2,eq_comm]

lemma indexedCommonDepth_self (n : ℕ) (l : IndexedLeaf n) :
    indexedCommonDepth n l l = Fin.last n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [indexedCommonDepth,ih]

lemma indexedLeafVertex_eq_iff (n : ℕ) (l m : IndexedLeaf n) (i : Fin n) :
    indexedLeafVertex n l i=indexedLeafVertex n m i ↔ i.val< (indexedCommonDepth n l m).val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    by_cases he : l.1=m.1 ∧ l.2.1=m.2.1
    · rcases he with ⟨h1,h2⟩
      rw [indexedCommonDepth,ite_eq_left ⟨h1,h2⟩]
      induction i using Fin.cases with
      | zero => simp [indexedLeafVertex,h1,h2]
      | succ i =>
        simpa [indexedLeafVertex,h1,h2] using ih l.2.2 m.2.2 i
    · rw [indexedCommonDepth,ite_eq_right he]
      induction i using Fin.cases <;> simp_all [indexedLeafVertex,Prod.mk.injEq]

lemma indexedLeafSharedVertex_eq_iff (n : ℕ) (l m : IndexedLeaf n) (i : Fin (n+1)) :
    indexedLeafSharedVertex n l i=indexedLeafSharedVertex n m i ↔ i ≤ indexedCommonDepth n l m := by
  induction i using Fin.cases with
  | zero => simp [indexedLeafSharedVertex]
  | succ i =>
    simpa only [indexedLeafSharedVertex,Fin.cases_succ,Sum.inr.injEq,
      Fin.le_iff_val_le_val,Fin.val_succ,Nat.succ_le_iff] using indexedLeafVertex_eq_iff n l m i

lemma indexedLeafSharedVertex_eq_iff_pair (n : ℕ) (l m : IndexedLeaf n) (i j : Fin (n+1)) :
    indexedLeafSharedVertex n l i=indexedLeafSharedVertex n m j ↔ i=j ∧ i ≤ indexedCommonDepth n l m := by
  constructor
  · intro h
    have he : i=j := by
      have hh := congrArg (indexedSharedVertexDepth n) h
      simpa only [indexedLeafSharedVertex_depth] using hh
    subst j
    exact ⟨rfl,(indexedLeafSharedVertex_eq_iff n l m i).mp h⟩
  · rintro ⟨rfl,h⟩
    exact (indexedLeafSharedVertex_eq_iff n l m i).mpr h

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma maskedGaussianCoefficient_sq_prefix (v : ℕ → S → ℝ) (L : S → ℕ) (n : ℕ) (x : S) :
    (∑ i : Fin n, maskedGaussianCoefficient v L i.val x^2) =
      ∑ i : Fin (min n (L x)), v i.val x^2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient v L i x^2) n,
    Fin.sum_univ_eq_sum_range (fun i => v i x^2) (min n (L x))]
  have he (i : ℕ) : maskedGaussianCoefficient v L i x^2 = if i<L x then v i x^2 else 0 := by
    unfold maskedGaussianCoefficient
    split_ifs <;> simp
  simp_rw [he]
  exact sum_range_cutoff _ n (L x)

omit [MeasurableSpace S] in
lemma maskedGaussianCoefficient_sq_bound (v : ℕ → S → ℝ) (L : S → ℕ)
    {D : ℝ} (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D) (n : ℕ) (x : S) :
    (∑ i : Fin n, maskedGaussianCoefficient v L i.val x^2) ≤ D := by
  rw [maskedGaussianCoefficient_sq_prefix]
  exact (gaussianCoefficient_prefix_sq_le v L n x).trans (hD x)

def gaussianPrefixCovariance (v w : ℕ → S → ℝ) (L : S → ℕ) (n : ℕ) (x y : S) : ℝ :=
  ∑ i : Fin n, maskedGaussianCoefficient w L i.val x*maskedGaussianCoefficient v L i.val y

def countableGaussianCovariance (v w : ℕ → S → ℝ) (L : S → ℕ) (x y : S) : ℝ :=
  gaussianPrefixCovariance v w L (L x) x y

lemma gaussianPrefixCovariance_measurable {v w : ℕ → S → ℝ} {L : S → ℕ}
    (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i)) (hL : Measurable L) (n : ℕ) :
    Measurable (Function.uncurry (gaussianPrefixCovariance v w L n)) := by
  unfold gaussianPrefixCovariance Function.uncurry
  exact Finset.measurable_sum _ fun i _ =>
    ((maskedGaussianCoefficient_measurable hw hL i.val).comp measurable_fst).mul
      ((maskedGaussianCoefficient_measurable hv hL i.val).comp measurable_snd)

lemma countableGaussianCovariance_measurable {v w : ℕ → S → ℝ} {L : S → ℕ}
    (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i)) (hL : Measurable L) :
    Measurable (Function.uncurry (countableGaussianCovariance v w L)) := by
  have hm : Measurable (fun p : ℕ×(S×S) => gaussianPrefixCovariance v w L p.1 p.2.1 p.2.2) := by
    apply measurable_from_prod_countable_right
    exact gaussianPrefixCovariance_measurable hv hw hL
  exact hm.comp ((hL.comp measurable_fst).prodMk measurable_id)

omit [MeasurableSpace S] in
lemma gaussianPrefixCovariance_bound (v w : ℕ → S → ℝ) (L : S → ℕ)
    {D E : ℝ} (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E) (n : ℕ) (x y : S) :
    |gaussianPrefixCovariance v w L n x y| ≤ (D+E)/2 := by
  have hi (i : Fin n) : |maskedGaussianCoefficient w L i.val x*maskedGaussianCoefficient v L i.val y| ≤
      (maskedGaussianCoefficient w L i.val x^2+maskedGaussianCoefficient v L i.val y^2)/2 := by
    rw [abs_mul]
    nlinarith [sq_abs (maskedGaussianCoefficient w L i.val x),
      sq_abs (maskedGaussianCoefficient v L i.val y),
      sq_nonneg (|maskedGaussianCoefficient w L i.val x|-|maskedGaussianCoefficient v L i.val y|)]
  calc
    _ ≤ ∑ i : Fin n, |maskedGaussianCoefficient w L i.val x*maskedGaussianCoefficient v L i.val y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, (maskedGaussianCoefficient w L i.val x^2+maskedGaussianCoefficient v L i.val y^2)/2 :=
      Finset.sum_le_sum fun i _ => hi i
    _ ≤ _ := by
      rw [← Finset.sum_div,Finset.sum_add_distrib]
      linarith [maskedGaussianCoefficient_sq_bound v L hD n y,maskedGaussianCoefficient_sq_bound w L hE n x]

omit [MeasurableSpace S] in
lemma gaussianPrefixCovariance_eventually_eq (v w : ℕ → S → ℝ) (L : S → ℕ) (x y : S) :
    ∀ᶠ n in atTop, gaussianPrefixCovariance v w L n x y=countableGaussianCovariance v w L x y := by
  filter_upwards [eventually_ge_atTop (L x)] with n hn
  unfold gaussianPrefixCovariance countableGaussianCovariance
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y) n]
  have he (i : ℕ) : maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y =
      if i<L x then w i x*maskedGaussianCoefficient v L i y else 0 := by
    unfold maskedGaussianCoefficient
    split_ifs <;> simp_all
  simp_rw [he]
  rw [sum_range_cutoff,min_eq_right hn]
  unfold gaussianPrefixCovariance
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y) (L x)]
  simp_rw [he,sum_range_cutoff,min_self]

end SphericalPerceptronFreeEnergy

end

end OAI
