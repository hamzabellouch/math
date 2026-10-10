import Mathlib
import OAI.Analysis.LaughlinFock.LadderCalculus

namespace OAI

/-! Tensor Basis. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

 
theorem highestWeight_swap {n z p : ℕ} (hn : z ≤ n) (hp : p ≤ z) :
    highestWeight n n z (z-p) = highestWeight n n z p := by
  unfold highestWeight
  rw [Nat.choose_symm hp, Nat.sub_sub_self hp,
    show n-(z-p) = n-z+p by omega, show n-z+(z-p) = n-p by omega]
  ring

 
theorem highestCoefficient_swap {n z p : ℕ} (hn : z ≤ n) (hp : p ≤ z) :
    highestCoefficient n n z (z-p) = (-1 : ℝ)^z * highestCoefficient n n z p := by
  have hs : (-1 : ℝ)^z * (-1 : ℝ)^(z-p) = (-1 : ℝ)^p := by
    calc
      _ = ((-1 : ℝ)^(z-p) * (-1 : ℝ)^(z-p)) * (-1 : ℝ)^p := by
        conv_lhs => lhs; rw [← Nat.sub_add_cancel hp, pow_add]
        ring
      _ = _ := by rw [← mul_pow]; norm_num
  unfold highestCoefficient
  rw [highestWeight_swap hn hp, Nat.sub_sub_self hp, ← mul_assoc, hs]

 

theorem coupledVector_swap {n z : ℕ} (hn : z ≤ n) (k p q : ℕ) :
    coupledVector n n z k q p = (-1 : ℝ)^z * coupledVector n n z k p q := by
  induction k generalizing p q with
  | zero =>
    by_cases h : p+q = z
    · have hp : p ≤ z := by omega
      have hq : q = z-p := by omega
      simp only [coupledVector, Nat.add_zero, coupledCoefficient,
        ite_eq_left h, ite_eq_left (by omega : q+p = z)]
      rw [hq, highestCoefficient_swap hn hp]
    · simp [coupledVector, h, show q+p ≠ z by omega]
  | succ k ih =>
    rw [coupledVector_succ (by omega : 2*z ≤ n+n)]
    simp only [Pi.smul_apply, smul_eq_mul, gridLower]
    rw [ih p (q-1), ih (p-1) q]
    ring

theorem coupledCoefficient_swap {n z : ℕ} (hn : z ≤ n) (k p : ℕ) (hp : p ≤ z+k) :
    coupledCoefficient n n z k (z+k-p) = (-1 : ℝ)^z * coupledCoefficient n n z k p := by
  simpa only [coupledVector, ite_eq_left (by omega : z+k-p+p = z+k),
    ite_eq_left (by omega : p+(z+k-p) = z+k)] using coupledVector_swap hn k p (z+k-p)

 

theorem coupledVector_antisymm {n z : ℕ} (hn : z ≤ n) (hz : Odd z) (k p q : ℕ) :
    coupledVector n n z k q p = -coupledVector n n z k p q := by
  rw [coupledVector_swap hn, hz.neg_one_pow, neg_one_mul]

theorem coupledVector_odd_diagonal {n z : ℕ} (hn : z ≤ n) (hz : Odd z) (k p : ℕ) :
    coupledVector n n z k p p = 0 := by
  have h := coupledVector_antisymm hn hz k p p
  linarith

 

abbrev CoupledIndex (n m : ℕ) :=
  (z : Fin (min n m + 1)) × Fin (n+m-2*z.val+1)

theorem sum_affine_integer (N : ℕ) (a : ℤ) :
    (∑ z ∈ Finset.range N, (a-2*z)) = (N : ℤ)*a - (N : ℤ)*((N : ℤ)-1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

 
theorem coupledIndex_card (n m : ℕ) :
    Fintype.card (CoupledIndex n m) = (n+1)*(m+1) := by
  have hc : (Fintype.card (CoupledIndex n m) : ℤ) = ((n : ℤ)+1)*((m : ℤ)+1) := by
    simp only [CoupledIndex, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    calc
      _ = ∑ z : Fin (min n m+1), ((n : ℤ)+m+1-2*z.val) := by
        apply Finset.sum_congr rfl
        intro z _
        have hz : 2*z.val ≤ n+m := by
          have h := z.isLt
          have h₁ := min_le_left n m
          have h₂ := min_le_right n m
          omega
        rw [Nat.cast_add, Nat.cast_sub hz]
        push_cast
        ring
      _ = ((min n m+1 : ℕ) : ℤ)*((n : ℤ)+m+1) -
          ((min n m+1 : ℕ) : ℤ)*(((min n m+1 : ℕ) : ℤ)-1) := by
        rw [Fin.sum_univ_eq_sum_range (fun z : ℕ => (n : ℤ)+m+1-2*z) (min n m+1), sum_affine_integer]
      _ = _ := by
        rcases le_total n m with h | h
        · rw [min_eq_left h]
          push_cast
          ring
        · rw [min_eq_right h]
          push_cast
          ring
  exact_mod_cast hc

def gridEuclidean (n m : ℕ) (f : GridVector) : EuclideanSpace ℝ (Fin (n+1) × Fin (m+1)) :=
  WithLp.toLp 2 (fun pq => f pq.1 pq.2)

theorem gridEuclidean_inner (n m : ℕ) (f g : GridVector) :
    inner ℝ (gridEuclidean n m f) (gridEuclidean n m g) = gridInner n m f g := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [gridEuclidean, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
  calc
    _ = ∑ p : Fin (n+1), ∑ q ∈ Finset.range (m+1), g p.val q * f p.val q := by
      apply Finset.sum_congr rfl
      intro p _
      exact Fin.sum_univ_eq_sum_range (fun q => g p.val q * f p.val q) (m+1)
    _ = ∑ p ∈ Finset.range (n+1), ∑ q ∈ Finset.range (m+1), g p q * f p q :=
      Fin.sum_univ_eq_sum_range (fun p => ∑ q ∈ Finset.range (m+1), g p q * f p q) (n+1)
    _ = _ := by simp only [gridInner, mul_comm]

 

def coupledEuclidean (n m : ℕ) (i : CoupledIndex n m) :
    EuclideanSpace ℝ (Fin (n+1) × Fin (m+1)) :=
  gridEuclidean n m (coupledVector n m i.1.val i.2.val)

theorem coupledIndex_bounds {n m : ℕ} (i : CoupledIndex n m) :
    i.1.val ≤ n ∧ i.1.val ≤ m ∧ i.2.val ≤ n+m-2*i.1.val := by
  have hz := i.1.isLt
  have hk := i.2.isLt
  have h₁ := min_le_left n m
  have h₂ := min_le_right n m
  omega

 

theorem coupledEuclidean_orthonormal (n m : ℕ) : Orthonormal ℝ (coupledEuclidean n m) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have hi := coupledIndex_bounds i
  have hj := coupledIndex_bounds j
  rw [coupledEuclidean, coupledEuclidean, gridEuclidean_inner,
    coupledVector_gram hi.1 hi.2.1 hj.1 hj.2.1 hi.2.2 hj.2.2]
  have he : (i.1.val = j.1.val ∧ i.2.val = j.2.val) ↔ i = j := by
    constructor
    · intro ⟨hz, hk⟩
      rcases i with ⟨z, k⟩
      rcases j with ⟨r, l⟩
      have hr : z = r := Fin.ext hz
      subst r
      have hl : k = l := Fin.ext hk
      subst l
      rfl
    · rintro rfl
      exact ⟨rfl, rfl⟩
  simp only [he]

 

def coupledBasis (n m : ℕ) :
    OrthonormalBasis (CoupledIndex n m) ℝ (EuclideanSpace ℝ (Fin (n+1) × Fin (m+1))) :=
  OrthonormalBasis.mk (coupledEuclidean_orthonormal n m)
    (((coupledEuclidean_orthonormal n m).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; exact coupledIndex_card n m)).ge)

@[simp] theorem coupledBasis_apply (n m : ℕ) (i : CoupledIndex n m) :
    coupledBasis n m i = coupledEuclidean n m i := by
  simp only [coupledBasis, OrthonormalBasis.coe_mk]

end LaughlinFock
end

end OAI
