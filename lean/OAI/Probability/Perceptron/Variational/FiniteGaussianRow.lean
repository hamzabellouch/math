import Mathlib
import OAI.Probability.Perceptron.Variational.IndexedGaussianMarks

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section
variable {K : Type*} [Fintype K]

def finiteGaussianRow (key : K → ℕ) (a : K → ℝ) (i : ℕ) : ℝ :=
  ∑ k, if key k = i then a k else 0

def finiteGaussianRowLength (key : K → ℕ) : ℕ :=
  Finset.univ.sup key + 1

lemma finiteGaussianRow_key {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ) (k : K) :
    finiteGaussianRow key a (key k) = a k := by
  classical
  simp [finiteGaussianRow,hk.eq_iff]

lemma finiteGaussianRow_zero {key : K → ℕ} (a : K → ℝ) (i : ℕ)
    (hi : ∀ k, key k ≠ i) : finiteGaussianRow key a i = 0 := by
  simp [finiteGaussianRow,hi]

lemma finiteGaussianRow_key_lt (key : K → ℕ) (k : K) :
    key k < finiteGaussianRowLength key :=
  Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ k))

lemma finiteGaussianRow_tail (key : K → ℕ) (a : K → ℝ) (i : ℕ)
    (hi : finiteGaussianRowLength key ≤ i) : finiteGaussianRow key a i = 0 := by
  apply finiteGaussianRow_zero a i
  intro k
  have h := finiteGaussianRow_key_lt key k
  omega

lemma finiteGaussianRow_sum {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ)
    (F : ℕ → ℝ → ℝ) (hF : ∀ i, F i 0 = 0) :
    (∑ i : Fin (finiteGaussianRowLength key), F i.val (finiteGaussianRow key a i.val)) =
      ∑ k, F (key k) (a k) := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i => F i (finiteGaussianRow key a i))]
  have hs : Finset.univ.image key ⊆ Finset.range (finiteGaussianRowLength key) := by
    intro i hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (finiteGaussianRow_key_lt key k)
  rw [← Finset.sum_subset hs]
  · rw [Finset.sum_image hk.injOn]
    simp_rw [finiteGaussianRow_key hk]
  · intro i hi hi'
    rw [finiteGaussianRow_zero a i,hF]
    intro k hki
    exact hi' (Finset.mem_image.mpr ⟨k,Finset.mem_univ k,hki⟩)

lemma finiteGaussianRow_field {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ) (g : ℕ → ℝ) :
    (∑ i : Fin (finiteGaussianRowLength key), g i.val*finiteGaussianRow key a i.val) =
      ∑ k, g (key k)*a k :=
  finiteGaussianRow_sum hk a (fun i x => g i*x) (fun _ => mul_zero _)

lemma finiteGaussianRow_norm {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ) :
    (∑ i : Fin (finiteGaussianRowLength key), finiteGaussianRow key a i.val^2) = ∑ k, a k^2 :=
  finiteGaussianRow_sum hk a (fun _ x => x^2) (fun _ => by norm_num)

end
variable {I : Type} [Fintype I]

def indexedGaussianRowKey (n : ℕ) (l : IndexedLeaf n) (p : Fin (n+1)×I) : ℕ :=
  countableCoordinate (indexedLeafSharedVertex n l p.1,p.2)

lemma indexedGaussianRowKey_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedGaussianRowKey (I := I) n l) := by
  intro a b hab
  have h := countableCoordinate_injective hab
  exact Prod.ext (indexedLeafSharedVertex_injective n l (congrArg Prod.fst h)) (congrArg (fun q : SharedVertex n × I => q.2) h)

variable {S : Type} [MeasurableSpace S]

def indexedGaussianRow (n : ℕ) (B : Fin (n+1) → I → ℝ) (V : S → EuclideanSpace ℝ I)
    (i : ℕ) (x : S×IndexedLeaf n) : ℝ :=
  finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => B p.1 p.2 * V x.1 p.2) i

def indexedGaussianRowLength (n : ℕ) (x : S×IndexedLeaf n) : ℕ :=
  finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)

lemma indexedGaussianRow_measurable (n : ℕ) (B : Fin (n+1) → I → ℝ)
    {V : S → EuclideanSpace ℝ I} (hV : Measurable V) (i : ℕ) :
    Measurable (indexedGaussianRow n B V i) := by
  apply measurable_from_prod_countable_left
  intro l
  unfold indexedGaussianRow finiteGaussianRow
  apply Finset.measurable_sum
  intro p hp
  by_cases hp : indexedGaussianRowKey n l p = i
  · simp only [ite_eq_left hp]
    fun_prop
  · simp only [ite_eq_right hp]
    exact measurable_const

lemma indexedGaussianRowLength_measurable (n : ℕ) :
    Measurable (indexedGaussianRowLength (S := S) (I := I) n) :=
  (measurable_of_countable (fun l : IndexedLeaf n =>
    finiteGaussianRowLength (indexedGaussianRowKey (I := I) n l))).comp measurable_snd

omit [MeasurableSpace S] in
lemma indexedGaussianRow_field (n : ℕ) (B : Fin (n+1) → I → ℝ) (V : S → EuclideanSpace ℝ I)
    (g : ℕ → ℝ) (x : S×IndexedLeaf n) :
    countableGaussianField (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) g x =
      ∑ d : Fin (n+1), ∑ i : I,
        g (countableCoordinate (indexedLeafSharedVertex n x.2 d,i))* (B d i * V x.1 i) := by
  rw [countableGaussianField,gaussianPrefixField]
  change (∑ i : Fin (finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)),
    g i.val * finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => B p.1 p.2 * V x.1 p.2) i.val) = _
  rw [finiteGaussianRow_field (indexedGaussianRowKey_injective n x.2),Fintype.sum_prod_type]
  rfl

omit [MeasurableSpace S] in
lemma indexedGaussianRow_norm (n : ℕ) (B : Fin (n+1) → I → ℝ) (V : S → EuclideanSpace ℝ I)
    (x : S×IndexedLeaf n) :
    (∑ i : Fin (indexedGaussianRowLength (I := I) n x), indexedGaussianRow n B V i.val x^2) =
      ∑ i : I, (∑ d : Fin (n+1), B d i^2) * V x.1 i^2 := by
  change (∑ i : Fin (finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)),
    finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => B p.1 p.2 * V x.1 p.2) i.val^2) = _
  rw [finiteGaussianRow_norm (indexedGaussianRowKey_injective n x.2),Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [mul_pow]
  rw [Finset.sum_mul]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_norm_le (n : ℕ) (B : Fin (n+1) → I → ℝ) (V : S → EuclideanSpace ℝ I)
    {C D : ℝ} (hC : ∀ i, (∑ d, B d i^2) ≤ C) (hC0 : 0 ≤ C)
    (hD : ∀ x, (∑ i, V x i^2) ≤ D) (x : S×IndexedLeaf n) :
    (∑ i : Fin (indexedGaussianRowLength (I := I) n x), indexedGaussianRow n B V i.val x^2) ≤ C*D := by
  rw [indexedGaussianRow_norm]
  calc
    _ ≤ ∑ i, C*V x.1 i^2 := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hC i) (sq_nonneg _)
    _ = C*∑ i, V x.1 i^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ C*D := mul_le_mul_of_nonneg_left (hD x.1) hC0

end SphericalPerceptronFreeEnergy

end

end OAI
