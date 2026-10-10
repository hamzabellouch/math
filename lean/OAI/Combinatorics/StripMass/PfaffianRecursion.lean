import Mathlib
import OAI.Combinatorics.StripMass.PfaffianMatrices

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial
lemma pfaffian_border {n : ℕ} (hn : Odd n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) :
    pfaffian (n + 1) (border A u) = borderLinear A u := by
  have hm : (n + 1) / 2 = n / 2 + 1 := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hz : twoForm A ^ (n / 2 + 1) = 0 :=
    high_degree_zero (by omega) _ (twoForm_pow_mem A (n / 2 + 1))
  have hcomm : Commute (ExteriorAlgebra.map (embedMap n) (twoForm A))
      (ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n)) :=
    (wedge_commutes _ _ _).symm
  unfold pfaffian
  change topCoord (n + 1) _ / _ = _
  rw [twoForm_border A hA, hm, pow_add_sq_zero _ _ hcomm (wedge_sq_zero _ _) (n / 2),
    ← map_pow, hz, map_zero, zero_add, map_smul, smul_eq_mul]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hm0 : (↑(n / 2) : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n / 2)
  rw [mul_div_mul_left _ _ hm0]
  rfl

lemma topCoord_embed_twice {n : ℕ} (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    topCoord (n + 2)
      (ExteriorAlgebra.map (embedMap (n + 1)) (ExteriorAlgebra.map (embedMap n) x) *
        (generator (n + 2) (Fin.last n).castSucc * generator (n + 2) (Fin.last (n + 1)))) =
      topCoord n x := by
  have ht : ExteriorAlgebra.map (embedMap (n + 1))
        (ExteriorAlgebra.map (embedMap n) (topWedge n)) *
        (generator (n + 2) (Fin.last n).castSucc * generator (n + 2) (Fin.last (n + 1))) =
      topWedge (n + 2) := by
    rw [← embedMap_generator (n + 1) (Fin.last n), ← mul_assoc, ← map_mul,
      ← topWedge_snoc, ← topWedge_snoc]
  conv_lhs => rw [homogeneous_eq_coord_topWedge n x hx]
  rw [map_smul, map_smul, smul_mul_assoc, ht, map_smul, topCoord_topWedge, smul_eq_mul, mul_one]

lemma pfaffian_block_pair {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    pfaffian (n + 2) (border (border A 0) (standardBasis (n + 1) (Fin.last n))) =
      pfaffian n A := by
  have hodd : Odd (n + 1) := hn.add_one
  have hm : (n + 1) / 2 = n / 2 := by obtain ⟨k, hk⟩ := hn; omega
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  rw [pfaffian_border hodd _ (border_skew A hA 0)]
  change topCoord (n + 2) _ / _ = _
  rw [twoForm_border A hA 0]
  simp only [map_zero, zero_mul, add_zero, embedMap_basis, hm, ← map_pow]
  change topCoord (n + 2)
    (ExteriorAlgebra.map (embedMap (n + 1)) (ExteriorAlgebra.map (embedMap n) (twoForm A ^ (n / 2))) *
      (generator (n + 2) (Fin.last n).castSucc * generator (n + 2) (Fin.last (n + 1)))) / _ = _
  rw [topCoord_embed_twice _ hhom]
  rfl

lemma borderLinear_column {n : ℕ} (hn : Odd n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (j : Fin n) :
    borderLinear A (fun i => A i j) = 0 := by
  rw [← pfaffian_border hn A hA]
  apply pfaffian_duplicate (n + 1) hn.add_one _ (border_skew A hA _)
    j.castSucc (Fin.last n) (Fin.castSucc_ne_last j)
  intro k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp only [border_old_last, border_last_last]
    have hj := hA j j
    linear_combination hj / 2
  · simp only [border_old_old, border_last_old]
    exact hA k j

lemma basis_last (n : ℕ) : standardBasis (n + 1) (Fin.last n) = Fin.snoc (fun _ => 0) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [standardBasis, Pi.basisFun_apply]

lemma pfaffian_zero_row (n : ℕ) (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (i : Fin n) (hrow : ∀ j, A i j = 0) :
    pfaffian n A = 0 := by
  let f : Vec n →ₗ[ℂ] Vec n :=
    (standardBasis n).constr ℂ (fun j => if j = i then 0 else standardBasis n j)
  have hf (j : Fin n) : f (standardBasis n j) = if j = i then 0 else standardBasis n j := by
    exact (standardBasis n).constr_basis ℂ _ j
  have hdet : f.det = 0 := by
    have hd := Module.Basis.det_comp (standardBasis n) f (standardBasis n)
    rw [Module.Basis.det_self, mul_one] at hd
    rw [← hd]
    exact (standardBasis n).det.map_coord_zero i (by simp [hf])
  have hcol (j : Fin n) : A j i = 0 := by rw [hA, hrow, neg_zero]
  have hform : ExteriorAlgebra.map f (twoForm A) = twoForm A := by
    unfold twoForm
    simp only [map_sum, map_smul, map_mul, generator, ExteriorAlgebra.map_apply_ι, hf]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hji : j = i
    · subst j
      simp [hrow]
    by_cases hki : k = i
    · subst k
      simp [hcol]
    simp [hji, hki]
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  have htop := topCoord_map n f (twoForm A ^ (n / 2)) hhom
  rw [map_pow, hform, hdet, zero_mul] at htop
  change topCoord n (twoForm A ^ (n / 2)) / _ = 0
  rw [htop, zero_div]

lemma pfaffian_block_extra {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) (t : ℂ) :
    pfaffian (n + 2) (border (border A 0) (Fin.snoc u t)) = t * pfaffian n A := by
  have hodd : Odd (n + 1) := hn.add_one
  have he : Fin.snoc u t = Fin.snoc u 0 + t • standardBasis (n + 1) (Fin.last n) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [basis_last]
  have hz : borderLinear (border A 0) (Fin.snoc u 0) = 0 := by
    rw [← pfaffian_border hodd _ (border_skew A hA 0)]
    apply pfaffian_zero_row (n + 2) (hodd.add_one) _
      (border_skew _ (border_skew A hA 0) _) (Fin.last n).castSucc
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  rw [pfaffian_border hodd _ (border_skew A hA 0), he, map_add, map_smul, hz, zero_add]
  rw [← pfaffian_border hodd _ (border_skew A hA 0), pfaffian_block_pair hn A hA, smul_eq_mul]

def lastSwap (n : ℕ) : Equiv.Perm (Fin (n + 2)) :=
  Equiv.swap (Fin.last n).castSucc (Fin.last (n + 1))

@[simp] lemma lastSwap_old (n : ℕ) (i : Fin n) :
    lastSwap n i.castSucc.castSucc = i.castSucc.castSucc := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact Fin.castSucc_ne_last i (Fin.castSucc_injective _ h)
  · exact Fin.castSucc_ne_last _

@[simp] lemma lastSwap_middle (n : ℕ) : lastSwap n (Fin.last n).castSucc = Fin.last (n + 1) := by
  simp [lastSwap]
@[simp] lemma lastSwap_last (n : ℕ) : lastSwap n (Fin.last (n + 1)) = (Fin.last n).castSucc := by
  simp [lastSwap]
@[simp] lemma lastSwap_symm (n : ℕ) : (lastSwap n).symm = lastSwap n := rfl

lemma border_swap_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u v : Vec n) (t : ℂ) :
    (fun i j => border (border A u) (Fin.snoc v t) ((lastSwap n).symm i) ((lastSwap n).symm j)) =
      border (border A v) (Fin.snoc u (-t)) := by
  funext i j
  simp only [lastSwap_symm]
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  · refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
  · refine Fin.lastCases ?_ (fun i => ?_) i <;>
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

lemma pfaffian_border_swap {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u v : Vec n) (t : ℂ) :
    pfaffian (n + 2) (border (border A v) (Fin.snoc u (-t))) =
      -pfaffian (n + 2) (border (border A u) (Fin.snoc v t)) := by
  have hp := pfaffian_perm (n + 2) (hn.add (by decide))
    (border (border A u) (Fin.snoc v t)) (border_skew _ (border_skew A hA u) _) (lastSwap n)
  rw [border_swap_matrix] at hp
  simpa [lastSwap, Equiv.Perm.sign_swap (Fin.castSucc_ne_last (Fin.last n))] using hp

lemma pfaffian_aug_pair {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) :
    pfaffian (n + 2) (border (border A u) (standardBasis (n + 1) (Fin.last n))) =
      pfaffian n A := by
  rw [basis_last]
  have hp := pfaffian_border_swap hn A hA u 0 1
  rw [pfaffian_block_extra hn A hA, neg_one_mul] at hp
  exact neg_injective hp.symm

lemma borderLinear_aug_ones {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    borderLinear (border A (fun _ => 1)) (fun _ => -1) = -pfaffian n A := by
  have hodd : Odd (n + 1) := hn.add_one
  have hz := borderLinear_column hodd (border A (fun _ => 1))
    (border_skew A hA _) (Fin.last n)
  have he : (fun _ : Fin (n + 1) => (-1 : ℂ)) =
      -(fun i => border A (fun _ => 1) i (Fin.last n)) - standardBasis (n + 1) (Fin.last n) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [basis_last]
  rw [he, map_sub, map_neg, hz, neg_zero, zero_sub]
  congr 1
  rw [← pfaffian_border hodd _ (border_skew A hA _), pfaffian_aug_pair hn A hA]

lemma D_symm (a b : ℂ) : D b a = D a b := by unfold D; ring
lemma kernel_skew (a b : ℂ) : kernel b a = -kernel a b := by
  unfold kernel
  rw [D_symm]
  ring
@[simp] lemma kernel_self (a : ℂ) : kernel a a = 0 := by simp [kernel]

def kernelMatrix (N : ℕ) (a : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => kernel (a i) (a j)

lemma kernelMatrix_skew (N : ℕ) (a : Fin N → ℂ) (i j : Fin N) :
    kernelMatrix N a j i = -kernelMatrix N a i j := kernel_skew _ _

lemma kernelMatrix_snoc (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    kernelMatrix (N + 1) (Fin.snoc a z) =
      border (kernelMatrix N a) (fun i => kernel (a i) z) := by
  funext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [kernelMatrix]
  exact kernel_skew _ _

lemma augmentedKernel_skew (N : ℕ) (a : Fin N → ℂ) (i j : Fin (pfSize N)) :
    augmentedKernel N a j i = -augmentedKernel N a i j := by
  by_cases hi : i.val < N <;> by_cases hj : j.val < N <;>
    simp only [augmentedKernel, hi, hj, dite_true, dite_false, ite_true, ite_false, neg_neg, neg_zero]
  exact kernel_skew _ _

def actualPf (N : ℕ) (a : Fin N → ℂ) : ℂ := pfaffian (pfSize N) (augmentedKernel N a)

lemma pfaffian_cast {m n : ℕ} (h : m = n) (A : Matrix (Fin m) (Fin m) ℂ) :
    pfaffian m A = pfaffian n (fun i j => A (Fin.cast h.symm i) (Fin.cast h.symm j)) := by
  subst n
  rfl

lemma actualPf_even {N : ℕ} (hN : Even N) (a : Fin N → ℂ) :
    actualPf N a = pfaffian N (kernelMatrix N a) := by
  have hs : pfSize N = N := by obtain ⟨k, hk⟩ := hN; unfold pfSize; omega
  unfold actualPf
  rw [pfaffian_cast hs]
  congr 1
  funext i j
  simp [augmentedKernel, kernelMatrix, i.isLt, j.isLt]

lemma actualPf_odd {N : ℕ} (hN : Odd N) (a : Fin N → ℂ) :
    actualPf N a = pfaffian (N + 1) (border (kernelMatrix N a) (fun _ => 1)) := by
  have hs : pfSize N = N + 1 := by obtain ⟨k, hk⟩ := hN; unfold pfSize; omega
  unfold actualPf
  rw [pfaffian_cast hs]
  congr 1
  funext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [augmentedKernel, kernelMatrix]

lemma actualPf_duplicate {N : ℕ} (a : Fin N → ℂ) (i j : Fin N)
    (hij : i ≠ j) (ha : a i = a j) : actualPf N a = 0 := by
  have hsize : N ≤ pfSize N := by unfold pfSize; omega
  let i' : Fin (pfSize N) := ⟨i.val, lt_of_lt_of_le i.isLt hsize⟩
  let j' : Fin (pfSize N) := ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩
  apply pfaffian_duplicate (pfSize N) (even_two_mul _) _ (augmentedKernel_skew N a) i' j'
  · intro h
    apply hij
    apply Fin.ext
    exact congrArg (fun k : Fin (pfSize N) => k.val) h
  · intro k
    simp only [augmentedKernel, i', j', i.isLt, j.isLt, dite_true]
    by_cases hk : k.val < N <;> simp [hk, ha]

def restrictMap (n : ℕ) : Vec (n + 1) →ₗ[ℂ] Vec n where
  toFun u i := u i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def flipLastMap (n : ℕ) : Vec (n + 1) →ₗ[ℂ] Vec (n + 1) where
  toFun u := Fin.snoc (fun i => u i.castSucc) (-u (Fin.last n))
  map_add' u v := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [add_comm]
  map_smul' t u := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [mul_neg]

@[simp] lemma restrictMap_snoc (n : ℕ) (u : Vec n) (t : ℂ) :
    restrictMap n (Fin.snoc u t) = u := by ext i; simp [restrictMap]
@[simp] lemma flipLastMap_snoc (n : ℕ) (u : Vec n) (t : ℂ) :
    flipLastMap n (Fin.snoc u t) = Fin.snoc u (-t) := by simp [flipLastMap]

def incrementLinear (N : ℕ) (a : Fin N → ℂ) : Vec (N + 1) →ₗ[ℂ] ℂ := by
  classical
  exact if Odd N then (borderLinear (kernelMatrix N a)).comp (restrictMap N)
    else -((borderLinear (border (kernelMatrix N a) (fun _ => 1))).comp (flipLastMap N))

lemma incrementLinear_eval (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    incrementLinear N a (Fin.snoc (fun i => kernel (a i) z) 1) =
      actualPf (N + 1) (Fin.snoc a z) := by
  by_cases hodd : Odd N
  · rw [incrementLinear, ite_eq_left hodd, LinearMap.comp_apply, restrictMap_snoc,
      actualPf_even hodd.add_one, kernelMatrix_snoc,
      pfaffian_border hodd _ (kernelMatrix_skew N a)]
  · have heven : Even N := Nat.not_odd_iff_even.mp hodd
    rw [incrementLinear, ite_eq_right hodd, LinearMap.neg_apply, LinearMap.comp_apply, flipLastMap_snoc,
      actualPf_odd heven.add_one, kernelMatrix_snoc]
    have hone : (fun _ : Fin (N + 1) => (1 : ℂ)) = Fin.snoc (fun _ => 1) 1 := by
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [hone, ← pfaffian_border heven.add_one _ (border_skew _ (kernelMatrix_skew N a) _),
      pfaffian_border_swap heven _ (kernelMatrix_skew N a), neg_neg]

lemma incrementLinear_leading (N : ℕ) (a : Fin N → ℂ) :
    incrementLinear N a (Fin.snoc (fun _ => -1) 1) = (-1 : ℂ) ^ N * actualPf N a := by
  by_cases hodd : Odd N
  · rw [incrementLinear, ite_eq_left hodd, LinearMap.comp_apply, restrictMap_snoc,
      actualPf_odd hodd, pfaffian_border hodd _ (kernelMatrix_skew N a), hodd.neg_one_pow]
    have he : (fun _ : Fin N => (-1 : ℂ)) = -(fun _ => 1) := rfl
    rw [he, map_neg, neg_one_mul]
  · have heven : Even N := Nat.not_odd_iff_even.mp hodd
    rw [incrementLinear, ite_eq_right hodd, LinearMap.neg_apply, LinearMap.comp_apply, flipLastMap_snoc,
      heven.neg_one_pow, one_mul, actualPf_even heven]
    have he : (Fin.snoc (fun _ : Fin N => (-1 : ℂ)) (-1 : ℂ) : Vec (N + 1)) =
        (fun _ : Fin (N + 1) => (-1 : ℂ)) := by
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [he, borderLinear_aug_ones heven _ (kernelMatrix_skew N a), neg_neg]

def polyLift {n : ℕ} (L : Vec n →ₗ[ℂ] ℂ) (f : Fin n → Polynomial ℂ) : Polynomial ℂ :=
  ∑ i, C (L (standardBasis n i)) * f i

lemma linear_basis_sum {n : ℕ} (L : Vec n →ₗ[ℂ] ℂ) (v : Vec n) :
    (∑ i, L (standardBasis n i) * v i) = L v := by
  have h := congrArg L ((standardBasis n).sum_repr v)
  simpa [standardBasis, Pi.basisFun_repr, map_sum, map_smul, smul_eq_mul, mul_comm] using h

lemma polyLift_eval {n : ℕ} (L : Vec n →ₗ[ℂ] ℂ) (f : Fin n → Polynomial ℂ) (z : ℂ) :
    (polyLift L f).eval z = L (fun i => (f i).eval z) := by
  simp only [polyLift, eval_finsetSum, eval_mul, eval_C]
  exact linear_basis_sum L _

lemma polyLift_coeff {n : ℕ} (L : Vec n →ₗ[ℂ] ℂ) (f : Fin n → Polynomial ℂ) (k : ℕ) :
    (polyLift L f).coeff k = L (fun i => (f i).coeff k) := by
  simp only [polyLift, finsetSum_coeff, coeff_C_mul]
  exact linear_basis_sum L _

lemma polyLift_degree {n k : ℕ} (L : Vec n →ₗ[ℂ] ℂ) (f : Fin n → Polynomial ℂ)
    (hf : ∀ i, (f i).natDegree ≤ k) : (polyLift L f).natDegree ≤ k := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_le _ _).trans (hf i)

def Dpoly (a : ℂ) : Polynomial ℂ := X ^ 2 + C (2 * d * a) * X + C (a ^ 2 - d ^ 2)
def pairNumerator (a : ℂ) : Polynomial ℂ := (C a - X) * (C (a + rho) + X)
def denominatorPoly (N : ℕ) (a : Fin N → ℂ) : Polynomial ℂ := ∏ i, Dpoly (a i)
def deletedDenominator (N : ℕ) (a : Fin N → ℂ) (i : Fin N) : Polynomial ℂ :=
  ∏ j ∈ Finset.univ.erase i, Dpoly (a j)
def kernelNumerator (N : ℕ) (a : Fin N → ℂ) (i : Fin N) : Polynomial ℂ :=
  pairNumerator (a i) * deletedDenominator N a i

def clearedPf (N : ℕ) (a : Fin N → ℂ) : Polynomial ℂ :=
  polyLift (incrementLinear N a) (Fin.snoc (kernelNumerator N a) (denominatorPoly N a))

@[simp] lemma Dpoly_eval (a z : ℂ) : (Dpoly a).eval z = D a z := by simp [Dpoly, D]; ring
lemma Dpoly_degree (a : ℂ) : (Dpoly a).natDegree ≤ 2 := by unfold Dpoly; compute_degree!
@[simp] lemma Dpoly_coeff (a : ℂ) : (Dpoly a).coeff 2 = 1 := by
  simp only [Dpoly, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num
lemma pairNumerator_degree (a : ℂ) : (pairNumerator a).natDegree ≤ 2 := by
  unfold pairNumerator
  compute_degree!
@[simp] lemma pairNumerator_coeff (a : ℂ) : (pairNumerator a).coeff 2 = -1 := by
  have h : (pairNumerator a).coeff (1 + 1) = (C a - X).coeff 1 * (C (a + rho) + X).coeff 1 := by
    apply coeff_mul_add_eq_of_natDegree_le <;> compute_degree!
  simpa using h

lemma denominatorPoly_degree (N : ℕ) (a : Fin N → ℂ) :
    (denominatorPoly N a).natDegree ≤ 2 * N := by
  apply (natDegree_prod_le _ _).trans
  calc ∑ i : Fin N, (Dpoly (a i)).natDegree ≤ ∑ _i : Fin N, 2 :=
        Finset.sum_le_sum (fun i _ => Dpoly_degree (a i))
    _ = 2 * N := by simp [mul_comm]

@[simp] lemma denominatorPoly_coeff (N : ℕ) (a : Fin N → ℂ) :
    (denominatorPoly N a).coeff (2 * N) = 1 := by
  have h := coeff_prod_of_natDegree_le (s := Finset.univ) (fun i => Dpoly (a i)) 2
    (fun i _ => Dpoly_degree (a i))
  simpa [denominatorPoly, mul_comm] using h

lemma deletedDenominator_degree (N : ℕ) (a : Fin N → ℂ) (i : Fin N) :
    (deletedDenominator N a i).natDegree ≤ 2 * (N - 1) := by
  apply (natDegree_prod_le _ _).trans
  calc ∑ j ∈ Finset.univ.erase i, (Dpoly (a j)).natDegree ≤ ∑ _j ∈ Finset.univ.erase i, 2 :=
        Finset.sum_le_sum (fun j _ => Dpoly_degree (a j))
    _ = 2 * (N - 1) := by simp [mul_comm]

@[simp] lemma deletedDenominator_coeff (N : ℕ) (a : Fin N → ℂ) (i : Fin N) :
    (deletedDenominator N a i).coeff (2 * (N - 1)) = 1 := by
  have h := coeff_prod_of_natDegree_le (s := Finset.univ.erase i) (fun j => Dpoly (a j)) 2
    (fun j _ => Dpoly_degree (a j))
  simpa [deletedDenominator, mul_comm] using h

lemma kernelNumerator_degree (N : ℕ) (a : Fin N → ℂ) (i : Fin N) :
    (kernelNumerator N a i).natDegree ≤ 2 * N := by
  have h := natDegree_mul_le.trans (add_le_add (pairNumerator_degree (a i))
    (deletedDenominator_degree N a i))
  have hi := i.isLt
  have hn : 2 + 2 * (N - 1) = 2 * N := by omega
  simpa [kernelNumerator, hn] using h

@[simp] lemma kernelNumerator_coeff (N : ℕ) (a : Fin N → ℂ) (i : Fin N) :
    (kernelNumerator N a i).coeff (2 * N) = -1 := by
  have h := coeff_mul_add_eq_of_natDegree_le (pairNumerator_degree (a i))
    (deletedDenominator_degree N a i)
  have hi := i.isLt
  have hn : 2 + 2 * (N - 1) = 2 * N := by omega
  simpa [kernelNumerator, hn] using h

lemma clearedPf_degree (N : ℕ) (a : Fin N → ℂ) : (clearedPf N a).natDegree ≤ 2 * N := by
  apply polyLift_degree
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using denominatorPoly_degree N a
  · simpa using kernelNumerator_degree N a j

lemma clearedPf_coeff (N : ℕ) (a : Fin N → ℂ) :
    (clearedPf N a).coeff (2 * N) = (-1 : ℂ) ^ N * actualPf N a := by
  rw [clearedPf, polyLift_coeff]
  convert incrementLinear_leading N a using 1
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

lemma denominatorPoly_eval (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    (denominatorPoly N a).eval z = ∏ i, D (a i) z := by simp only [denominatorPoly, eval_prod, Dpoly_eval]

lemma deletedDenominator_mul (N : ℕ) (a : Fin N → ℂ) (i : Fin N) :
    deletedDenominator N a i * Dpoly (a i) = denominatorPoly N a := by
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)

lemma kernelNumerator_eval (N : ℕ) (a : Fin N → ℂ) (z : ℂ)
    (hz : ∀ i, D (a i) z ≠ 0) (i : Fin N) :
    (kernelNumerator N a i).eval z = (denominatorPoly N a).eval z * kernel (a i) z := by
  have h := congrArg (Polynomial.eval z) (deletedDenominator_mul N a i)
  simp only [eval_mul, Dpoly_eval] at h
  simp only [kernelNumerator, pairNumerator, eval_mul, eval_sub, eval_add, eval_C, eval_X, kernel]
  rw [← h]
  field_simp [hz i]
  ring

end
end StripPfaffian

end OAI
