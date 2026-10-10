import Mathlib
import OAI.LinearAlgebra.MatrixFields.Arithmetic.ComplexArithmeticExponent
import OAI.LinearAlgebra.MatrixFields.Arithmetic.ComplexArithmeticGrowth
import OAI.LinearAlgebra.MatrixFields.Entropy.ComplexAsymptoticRecurrence
import OAI.LinearAlgebra.MatrixFields.Entropy.ComplexPolynomialPowerGrowth

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {F X Y Z : Type*} [Field F]

theorem coeff_eq_sum_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → F) (hnodes : Function.Injective nodes)
    (p : Polynomial F) (d : ℕ) (hdegree : p.degree < Fintype.card ι) :
    p.coeff d = ∑ i, p.eval (nodes i) *
      (Lagrange.basis Finset.univ nodes i).coeff d := by
  have hinj : Set.InjOn nodes (↑(Finset.univ : Finset ι)) := hnodes.injOn
  have hinterp := Lagrange.eq_interpolate hinj (by simpa using hdegree)
    (f := p)
  calc
    p.coeff d = (Lagrange.interpolate Finset.univ nodes
        (fun i => p.eval (nodes i))).coeff d := congrArg (fun q => q.coeff d) hinterp
    _ = _ := by
      simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul]

theorem RankAtMost.coeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → F) (hnodes : Function.Injective nodes)
    {P : Tensor (Polynomial F) X Y Z} {r : ℕ} (hP : RankAtMost P r)
    (d : ℕ) (hdegree : ∀ x y z, (P x y z).degree < Fintype.card ι) :
    RankAtMost (fun x y z => (P x y z).coeff d) (Fintype.card ι * r) := by
  rcases hP with ⟨a, b, c, rfl⟩
  let w : ι → F := fun i => (Lagrange.basis Finset.univ nodes i).coeff d
  let aa : (ι × Fin r) → X → F := fun i x => w i.1 * (a i.2 x).eval (nodes i.1)
  let bb : (ι × Fin r) → Y → F := fun i y => (b i.2 y).eval (nodes i.1)
  let cc : (ι × Fin r) → Z → F := fun i z => (c i.2 z).eval (nodes i.1)
  have heq : (fun x y z => (∑ j, rankOne (a j) (b j) (c j) x y z).coeff d) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    rw [coeff_eq_sum_eval nodes hnodes _ d (hdegree x y z)]
    simp only [Fintype.sum_prod_type, rankOne, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [aa, bb, cc, w]
    ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

structure PolynomialApproximation (T : Tensor F X Y Z) (r d D : ℕ) where
  polynomial : Tensor (Polynomial F) X Y Z
  rank_bound : RankAtMost polynomial r
  vanishes : ∀ x y z k, k < d → (polynomial x y z).coeff k = 0
  leading : ∀ x y z, (polynomial x y z).coeff d = T x y z
  degree_bound : ∀ x y z, (polynomial x y z).degree ≤ D

namespace PolynomialApproximation

variable {T : Tensor F X Y Z} {r d D : ℕ}

def normalized (A : PolynomialApproximation T r d D) :
    Tensor (Polynomial F) X Y Z :=
  fun x y z => Classical.choose (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x y z))

theorem polynomial_eq (A : PolynomialApproximation T r d D) (x : X) (y : Y) (z : Z) :
    A.polynomial x y z = Polynomial.X ^ d * A.normalized x y z :=
  Classical.choose_spec (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x y z))

theorem normalized_constant (A : PolynomialApproximation T r d D)
    (x : X) (y : Y) (z : Z) : (A.normalized x y z).coeff 0 = T x y z := by
  have h := A.leading x y z
  rw [A.polynomial_eq] at h
  simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self] using h

theorem power_polynomial_eq (A : PolynomialApproximation T r d D) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) :
    Tensor.power A.polynomial n x y z =
      Polynomial.X ^ (d * n) * Tensor.power A.normalized n x y z := by
  simp [Tensor.power, A.polynomial_eq, Finset.prod_mul_distrib, ← pow_mul]

def power (A : PolynomialApproximation T r d D) (n : ℕ) :
    PolynomialApproximation (Tensor.power T n) (r ^ n) (d * n) (D * n) where
  polynomial := Tensor.power A.polynomial n
  rank_bound := A.rank_bound.power n
  vanishes := by
    intro x y z k hk
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hk, ite_false]
  leading := by
    intro x y z
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
      Tensor.power, Polynomial.coeff_zero_prod, A.normalized_constant]
  degree_bound := by
    intro x y z
    apply Polynomial.degree_le_of_natDegree_le
    calc
      (Tensor.power A.polynomial n x y z).natDegree ≤
          ∑ i, (A.polynomial (x i) (y i) (z i)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _i : Fin n, D := by
        apply Finset.sum_le_sum
        intro i hi
        exact Polynomial.natDegree_le_of_degree_le (A.degree_bound (x i) (y i) (z i))
      _ = D * n := by simp [Nat.mul_comm]

theorem rank_power [CharZero F] (A : PolynomialApproximation T r d D) (n : ℕ) :
    RankAtMost (Tensor.power T n) ((D * n + 1) * r ^ n) := by
  let nodes : Fin (D * n + 1) → F := fun i => (i.val : F)
  have hinj : Function.Injective nodes := by
    intro i j h
    apply Fin.ext
    exact Nat.cast_injective h
  have hdegree (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) :
      ((A.power n).polynomial x y z).degree < Fintype.card (Fin (D * n + 1)) := by
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt ((A.power n).degree_bound x y z)
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (D * n)))
  have h := (A.power n).rank_bound.coeff nodes hinj (d * n) hdegree
  have heq : (fun x y z => ((A.power n).polynomial x y z).coeff (d * n)) =
      Tensor.power T n := by
    funext x y z
    exact (A.power n).leading x y z
  rw [heq, Fintype.card_fin] at h
  exact h

theorem rank_normalized_eval (A : PolynomialApproximation T r d D)
    (t : F) (ht : t ≠ 0) :
    RankAtMost (fun x y z => (A.normalized x y z).eval t) r := by
  have h := (A.rank_bound.map (Polynomial.evalRingHom t)).scale ((t ^ d)⁻¹)
  change RankAtMost (fun x y z => (t ^ d)⁻¹ * (A.polynomial x y z).eval t) r at h
  have heq : (fun x y z => (t ^ d)⁻¹ * (A.polynomial x y z).eval t) =
      fun x y z => (A.normalized x y z).eval t := by
    funext x y z
    rw [A.polynomial_eq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d ht), one_mul]
  rw [heq] at h
  exact h

theorem borderRankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    {S : Tensor ℂ X Y Z} (A : PolynomialApproximation S r d D) :
    BorderRankAtMost S r := by
  let f : ℂ → Tensor ℂ X Y Z := fun t x y z => (A.normalized x y z).eval t
  have hf : Continuous f := by
    apply continuous_pi
    intro x
    apply continuous_pi
    intro y
    apply continuous_pi
    intro z
    exact (A.normalized x y z).continuous
  have hclosed : IsClosed {t : ℂ | BorderRankAtMost (f t) r} :=
    isClosed_closure.preimage hf
  have hsubset : ({0}ᶜ : Set ℂ) ⊆ {t : ℂ | BorderRankAtMost (f t) r} := by
    intro t ht
    exact (A.rank_normalized_eval t (by simpa using ht)).borderRankAtMost
  have hz := closure_minimal hsubset hclosed ((dense_compl_singleton (0 : ℂ)) 0)
  have heq : f 0 = S := by
    funext x y z
    simp only [f, ← Polynomial.coeff_zero_eq_eval_zero, A.normalized_constant]
  change BorderRankAtMost (f 0) r at hz
  rw [heq] at hz
  exact hz

end PolynomialApproximation

end Tensor
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

def batchCount (R k : ℕ) : ℕ := (R + k - 1) / k

@[simp] theorem batchCount_zero (k : ℕ) : batchCount 0 k = 0 := by
  unfold batchCount
  by_cases hk : k = 0
  · simp [hk]
  · apply Nat.div_eq_of_lt
    omega

theorem le_batchCount_mul (R : ℕ) {k : ℕ} (hk : 0 < k) :
    R ≤ batchCount R k * k := by
  have hdiv := Nat.div_add_mod (R + k - 1) k
  have hmod := Nat.mod_lt (R + k - 1) hk
  rw [Nat.mul_comm k ((R + k - 1) / k)] at hdiv
  unfold batchCount
  omega

theorem batchCount_le_iff {R k B : ℕ} (hk : 0 < k) :
    batchCount R k ≤ B ↔ R ≤ B * k := by
  unfold batchCount
  rw [Nat.div_le_iff_le_mul hk]
  omega

theorem batchCount_mul_lt (R : ℕ) {k : ℕ} (hk : 0 < k) :
    batchCount R k * k < R + k := by
  have hmul := Nat.div_mul_le_self (R + k - 1) k
  unfold batchCount
  omega

theorem batchCount_pos_iff {R k : ℕ} (hk : 0 < k) :
    0 < batchCount R k ↔ 0 < R := by
  have hzero := batchCount_le_iff (R := R) (B := 0) hk
  simp only [Nat.zero_mul] at hzero
  omega

theorem batchCount_cast_lt (R : ℕ) {k : ℕ} (hk : 0 < k) :
    (batchCount R k : ℝ) < (R : ℝ) / (k : ℝ) + 1 := by
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hmul : (batchCount R k : ℝ) * (k : ℝ) < (R : ℝ) + (k : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using
      (Nat.cast_lt (α := ℝ)).mpr (batchCount_mul_lt R hk)
  calc
    (batchCount R k : ℝ) < ((R : ℝ) + (k : ℝ)) / (k : ℝ) :=
      (lt_div_iff₀ hkR).mpr hmul
    _ = (R : ℝ) / (k : ℝ) + 1 := by rw [add_div, div_self (ne_of_gt hkR)]

theorem batchCount_cast_le (R : ℕ) {k : ℕ} (hk : 0 < k) :
    (batchCount R k : ℝ) ≤ (R : ℝ) / (k : ℝ) + 1 :=
  (batchCount_cast_lt R hk).le

theorem batchCount_mul_cast_le (R r : ℕ) {k : ℕ} (hk : 0 < k) :
    ((batchCount R k * r : ℕ) : ℝ) ≤
      (r : ℝ) / (k : ℝ) * (R : ℝ) + (r : ℝ) := by
  calc
    ((batchCount R k * r : ℕ) : ℝ) = (batchCount R k : ℝ) * (r : ℝ) := by
      rw [Nat.cast_mul]
    _ ≤ ((R : ℝ) / (k : ℝ) + 1) * (r : ℝ) :=
      mul_le_mul_of_nonneg_right (batchCount_cast_le R hk) (Nat.cast_nonneg r)
    _ = (r : ℝ) / (k : ℝ) * (R : ℝ) + (r : ℝ) := by
      simp only [div_eq_mul_inv]
      ring

def batchRank (k r : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => batchCount (batchRank k r t) k * r

@[simp] theorem batchRank_zero (k r : ℕ) : batchRank k r 0 = 1 := rfl

@[simp] theorem batchRank_succ (k r t : ℕ) :
    batchRank k r (t + 1) = batchCount (batchRank k r t) k * r := rfl

theorem batchRank_succ_le_affine {k : ℕ} (hk : 0 < k) (r t : ℕ) :
    (batchRank k r (t + 1) : ℝ) ≤
      (r : ℝ) / (k : ℝ) * (batchRank k r t : ℝ) + (r : ℝ) := by
  rw [batchRank_succ]
  exact batchCount_mul_cast_le (batchRank k r t) r hk

theorem batchRank_pos {k r : ℕ} (hk : 0 < k) (hr : 0 < r) :
    ∀ t, 0 < batchRank k r t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [batchRank_succ]
    exact Nat.mul_pos ((batchCount_pos_iff hk).mpr ih) hr

namespace Tensor

variable {K X Y Z U V W A B : Type*} [CommSemiring K]

theorem RankAtMost.repeat_batch_ceiling {S : Tensor K U V W} {k r R : ℕ}
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r) (hk : 0 < k) :
    RankAtMost (directSum (fun _ : Fin R => S)) (batchCount R k * r) :=
  hbatch.repeat_batch (le_batchCount_mul R hk)

theorem RankAtMost.batch_product_ceiling [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {R k r : ℕ}
    (hT : RankAtMost T R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r) (hk : 0 < k) :
    RankAtMost (Tensor.product T S) (batchCount R k * r) :=
  hT.batch_product hbatch (le_batchCount_mul R hk)

theorem matrixCoefficients_batch_rank_ceiling [DecidableEq A] [DecidableEq B] [Fintype B]
    {R k r : ℕ}
    (houter : RankAtMost (matrixCoefficients (K := K) A A A) R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => matrixCoefficients (K := K) B B B)) r)
    (hk : 0 < k) :
    RankAtMost (matrixCoefficients (K := K) (A × B) (A × B) (A × B))
      (batchCount R k * r) :=
  matrixCoefficients_batch_rank houter hbatch (le_batchCount_mul R hk)

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

namespace Tensor

theorem matrixCoefficients_rank_of_injective {K A B : Type*} [CommSemiring K]
    [DecidableEq A] [DecidableEq B] {R : ℕ}
    (h : RankAtMost (matrixCoefficients (K := K) A A A) R)
    (f : B → A) (hf : Function.Injective f) :
    RankAtMost (matrixCoefficients (K := K) B B B) R := by
  have hp := h.pullback (fun x : B × B => (f x.1, f x.2))
    (fun y : B × B => (f y.1, f y.2))
    (fun z : B × B => (f z.1, f z.2))
  convert hp using 1
  funext x y z
  simp only [pullback, matrixCoefficients, hf.eq_iff]

theorem matrixCoefficients_directSum_rank_of_injective
    {K ι κ A B : Type*} [CommSemiring K]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq A] [DecidableEq B] {R : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A A A)) R)
    (f : κ → ι) (hf : Function.Injective f) (g : B → A) (hg : Function.Injective g) :
    RankAtMost (directSum (fun _ : κ => matrixCoefficients (K := K) B B B)) R := by
  have hp := h.pullback
    (fun x : κ × (B × B) => (f x.1, (g x.2.1, g x.2.2)))
    (fun y : κ × (B × B) => (f y.1, (g y.2.1, g y.2.2)))
    (fun z : κ × (B × B) => (f z.1, (g z.2.1, g z.2.2)))
  convert hp using 1
  funext x y z
  simp only [pullback, directSum, matrixCoefficients, hf.eq_iff, hg.eq_iff]

theorem matrixCoefficients_directSum_power_rank {K : Type*} [CommSemiring K]
    {n k R t : ℕ}
    (h : RankAtMost (power (directSum
      (fun _ : Fin k => matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))) t) R) :
    RankAtMost (directSum (fun _ : Fin (k ^ t) =>
      matrixCoefficients (K := K) (Fin (n ^ t)) (Fin (n ^ t)) (Fin (n ^ t)))) R := by
  have hmatrix := matrixCoefficients_directSum_rank_of_power h
  let tags : Fin (k ^ t) ≃ (Fin t → Fin k) := Fintype.equivOfCardEq (by simp)
  let indices : Fin (n ^ t) ≃ (Fin t → Fin n) := Fintype.equivOfCardEq (by simp)
  exact matrixCoefficients_directSum_rank_of_injective hmatrix
    tags tags.injective indices indices.injective

theorem PolynomialApproximation.square_directSum_power_rank
    {n k r d D : ℕ}
    (A : PolynomialApproximation
      (directSum (fun _ : Fin k => matrixMultiplication n n n)) r d D) (t : ℕ) :
    RankAtMost (directSum (fun _ : Fin (k ^ t) =>
      matrixMultiplication (n ^ t) (n ^ t) (n ^ t))) ((D * t + 1) * r ^ t) :=
  matrixCoefficients_directSum_power_rank (A.rank_power t)

theorem matrixCoefficients_fin_one_rank {K : Type*} [CommSemiring K] :
    RankAtMost (matrixCoefficients (K := K) (Fin 1) (Fin 1) (Fin 1)) 1 := by
  have heq : matrixCoefficients (K := K) (Fin 1) (Fin 1) (Fin 1) =
      rankOne (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
    funext x y z
    have hxy : x.2 = y.1 := Subsingleton.elim _ _
    have hyz : y.2 = z.1 := Subsingleton.elim _ _
    have hzx : z.2 = x.1 := Subsingleton.elim _ _
    simp [matrixCoefficients, rankOne, hxy, hyz, hzx]
  rw [heq]
  exact rankOne_rankAtMost _ _ _

theorem matrixCoefficients_pow_batchRank {K : Type*} [CommSemiring K]
    {n k r : ℕ} (hk : 0 < k)
    (hbatch : RankAtMost
      (directSum (fun _ : Fin k => matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))) r) :
    ∀ t : ℕ, RankAtMost
      (matrixCoefficients (K := K) (Fin (n ^ t)) (Fin (n ^ t)) (Fin (n ^ t)))
      (batchRank k r t) := by
  intro t
  induction t with
  | zero =>
    simp only [batchRank_zero]
    exact matrixCoefficients_fin_one_rank
  | succ t ih =>
    let e : Fin (n ^ (t + 1)) ≃ Fin (n ^ t) × Fin n :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    have hp := matrixCoefficients_batch_rank_ceiling ih hbatch hk
    have hr := matrixCoefficients_rank_of_injective hp e e.injective
    simpa only [batchRank_succ] using hr

end Tensor

namespace Arithmetic

theorem rpow_omega_le_of_rankAtMost {n R : ℕ} {B : ℝ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R)
    (hquad : (n : ℝ) ^ 2 ≤ B) (hR : (R : ℝ) ≤ B) :
    (n : ℝ) ^ omega ≤ B := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn0 : 0 < (n : ℝ) := lt_trans zero_lt_one hn1
  have hB : 0 < B := (sq_pos_of_pos hn0).trans_le hquad
  have hpow : (n : ℝ) ^ Real.logb n B = B :=
    Real.rpow_logb hn0 (ne_of_gt hn1) hB
  have hτ : 2 ≤ Real.logb (n : ℝ) B := by
    apply (Real.le_logb_iff_rpow_le hn1 hB).mpr
    simpa only [Real.rpow_two] using hquad
  have hadmissible := admissibleExponent_of_rankAtMost hn hRank hτ (hR.trans_eq hpow.symm)
  exact (Real.rpow_le_rpow_of_exponent_le hn1.le
    (omega_le_of_admissibleExponent hadmissible)).trans_eq hpow

theorem rpow_omega_le_of_rank_growth {n : ℕ} {q C : ℝ} (hn : 2 ≤ n)
    (hquad : (n : ℝ) ^ 2 ≤ q) (R : ℕ → ℕ)
    (hRank : ∀ t : ℕ, Tensor.RankAtMost
      (Tensor.matrixMultiplication (n ^ t) (n ^ t) (n ^ t)) (R t))
    (hcost : ∀ t : ℕ, (R t : ℝ) ≤ C * q ^ t) :
    (n : ℝ) ^ omega ≤ q := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hq0 : 0 ≤ q := (sq_nonneg (n : ℝ)).trans hquad
  apply power_le_of_forall_pow_le_mul_pow hq0 (C := max 1 C)
  intro t ht
  have hnt : 2 ≤ n ^ t := hn.trans (le_self_pow (by omega) (Nat.ne_of_gt ht))
  have hbase : ((n ^ t : ℕ) : ℝ) ^ 2 ≤ max 1 C * q ^ t := by
    calc
      ((n ^ t : ℕ) : ℝ) ^ 2 = ((n : ℝ) ^ 2) ^ t := by
        rw [Nat.cast_pow, ← pow_mul, ← pow_mul, Nat.mul_comm t 2]
      _ ≤ q ^ t := by gcongr
      _ ≤ max 1 C * q ^ t := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C) (pow_nonneg hq0 t)
  have hcost' : (R t : ℝ) ≤ max 1 C * q ^ t :=
    (hcost t).trans (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C)
      (pow_nonneg hq0 t))
  have h := rpow_omega_le_of_rankAtMost hnt (hRank t) hbase hcost'
  simpa only [Nat.cast_pow, ← Real.rpow_pow_comm hn0] using h

theorem equalSummand_inequality_of_quadratic_bound {n k r : ℕ}
    (hn : 2 ≤ n) (hk : 0 < k)
    (hbatch : Tensor.RankAtMost
      (Tensor.directSum (fun _ : Fin k => Tensor.matrixMultiplication n n n)) r)
    (hquad : (n : ℝ) ^ 2 ≤ (r : ℝ) / (k : ℝ)) :
    (k : ℝ) * (n : ℝ) ^ omega ≤ (r : ℝ) := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 1 < (r : ℝ) / (k : ℝ) := by nlinarith
  have hRank := Tensor.matrixCoefficients_pow_batchRank hk hbatch
  have hcost := affine_recurrence_bound (fun t => (batchRank k r t : ℝ))
    ((r : ℝ) / (k : ℝ)) (r : ℝ) hq (Nat.cast_nonneg r)
    (fun t => batchRank_succ_le_affine hk r t)
  have hbound : (n : ℝ) ^ omega ≤ (r : ℝ) / (k : ℝ) := by
    apply rpow_omega_le_of_rank_growth
      (C := (batchRank k r 0 : ℝ) + (r : ℝ) / ((r : ℝ) / (k : ℝ) - 1))
      hn hquad (batchRank k r)
    · exact hRank
    · intro t
      exact (hcost t).trans_eq (mul_comm _ _)
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  simpa only [mul_comm] using (le_div_iff₀ hkreal).mp hbound

theorem equalSummand_inequality {n k r : ℕ} (hn : 1 ≤ n)
    (hbatch : Tensor.RankAtMost
      (Tensor.directSum (fun _ : Fin k => Tensor.matrixMultiplication n n n)) r) :
    (k : ℝ) * (n : ℝ) ^ omega ≤ (r : ℝ) := by
  have hlower := Tensor.directSum_square_rank_lower k n r (by omega) hbatch
  by_cases hn1 : n = 1
  · subst n
    simpa only [Nat.cast_one, Real.one_rpow, mul_one, one_pow] using
      (show (k : ℝ) ≤ (r : ℝ) by exact_mod_cast (by simpa using hlower : k ≤ r))
  by_cases hk0 : k = 0
  · subst k
    simp
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  apply equalSummand_inequality_of_quadratic_bound (by omega) hk hbatch
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (le_div_iff₀ hkreal).mpr
  have hlower_real : (k : ℝ) * (n : ℝ) ^ 2 ≤ (r : ℝ) := by exact_mod_cast hlower
  simpa only [mul_comm] using hlower_real

theorem equalSummand_inequality_of_polynomialApproximation {n k r d D : ℕ}
    (hn : 1 ≤ n)
    (A : Tensor.PolynomialApproximation
      (Tensor.directSum (fun _ : Fin k => Tensor.matrixMultiplication n n n)) r d D) :
    (k : ℝ) * (n : ℝ) ^ omega ≤ (r : ℝ) := by
  apply power_le_of_forall_pow_le_linear_mul_pow D (Nat.cast_nonneg r)
  intro t ht
  have hnt : 1 ≤ n ^ t := pow_pos (by omega : 0 < n) t
  have h := equalSummand_inequality hnt (A.square_directSum_power_rank t)
  simpa only [Nat.cast_pow, Nat.cast_mul, mul_pow,
    ← Real.rpow_pow_comm (Nat.cast_nonneg n)] using h

end Arithmetic

end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

namespace Tensor

open MatrixMultiplication.Foundation.Tensor

theorem rectangular_rank_of_injective
    {K A B C A' B' C' : Type*} [CommSemiring K]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq A'] [DecidableEq B'] [DecidableEq C'] {R : ℕ}
    (h : RankAtMost (matrixCoefficients (K := K) A B C) R)
    (f : A' → A) (hf : Function.Injective f)
    (g : B' → B) (hg : Function.Injective g)
    (j : C' → C) (hj : Function.Injective j) :
    RankAtMost (matrixCoefficients (K := K) A' B' C') R := by
  have hp := h.pullback (fun x : A' × B' => (f x.1, g x.2))
    (fun y : B' × C' => (g y.1, j y.2))
    (fun z : C' × A' => (j z.1, f z.2))
  convert hp using 1
  funext x y z
  simp only [pullback, matrixCoefficients, hf.eq_iff, hg.eq_iff, hj.eq_iff]

theorem rectangular_directSum_rank_of_injective
    {K ι κ A B C A' B' C' : Type*} [CommSemiring K]
    [DecidableEq ι] [DecidableEq κ]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq A'] [DecidableEq B'] [DecidableEq C'] {R : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) R)
    (e : κ → ι) (he : Function.Injective e)
    (f : A' → A) (hf : Function.Injective f)
    (g : B' → B) (hg : Function.Injective g)
    (j : C' → C) (hj : Function.Injective j) :
    RankAtMost (directSum (fun _ : κ => matrixCoefficients (K := K) A' B' C')) R := by
  have hp := h.pullback
    (fun x : κ × (A' × B') => (e x.1, (f x.2.1, g x.2.2)))
    (fun y : κ × (B' × C') => (e y.1, (g y.2.1, j y.2.2)))
    (fun z : κ × (C' × A') => (e z.1, (j z.2.1, f z.2.2)))
  convert hp using 1
  funext x y z
  simp only [pullback, directSum, matrixCoefficients,
    he.eq_iff, hf.eq_iff, hg.eq_iff, hj.eq_iff]

theorem rectangular_directSum_power_rank {K : Type*} [CommSemiring K]
    {a b c L R t : ℕ}
    (h : RankAtMost (power (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) t) R) :
    RankAtMost (directSum (fun _ : Fin (L ^ t) =>
      matrixCoefficients (K := K) (Fin (a ^ t)) (Fin (b ^ t)) (Fin (c ^ t)))) R := by
  have hmatrix := matrixCoefficients_directSum_rank_of_power h
  let tags : Fin (L ^ t) ≃ (Fin t → Fin L) := Fintype.equivOfCardEq (by simp)
  let rows : Fin (a ^ t) ≃ (Fin t → Fin a) := Fintype.equivOfCardEq (by simp)
  let inner : Fin (b ^ t) ≃ (Fin t → Fin b) := Fintype.equivOfCardEq (by simp)
  let cols : Fin (c ^ t) ≃ (Fin t → Fin c) := Fintype.equivOfCardEq (by simp)
  exact rectangular_directSum_rank_of_injective hmatrix tags tags.injective
    rows rows.injective inner inner.injective cols cols.injective

theorem rectangular_pow_batchRank {K : Type*} [CommSemiring K]
    {a b c L r : ℕ} (hL : 0 < L)
    (hbatch : RankAtMost (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) r) :
    ∀ t : ℕ, RankAtMost
      (matrixCoefficients (K := K) (Fin (a ^ t)) (Fin (b ^ t)) (Fin (c ^ t)))
      (batchRank L r t) := by
  intro t
  induction t with
  | zero =>
    simp only [batchRank_zero]
    exact matrixCoefficients_fin_one_rank
  | succ t ih =>
    let rows : Fin (a ^ (t + 1)) ≃ Fin (a ^ t) × Fin a :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    let inner : Fin (b ^ (t + 1)) ≃ Fin (b ^ t) × Fin b :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    let cols : Fin (c ^ (t + 1)) ≃ Fin (c ^ t) × Fin c :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    have hp := matrixCoefficients_rank_of_product (ih.batch_product_ceiling hbatch hL)
    have hr := rectangular_rank_of_injective hp
      rows rows.injective inner inner.injective cols cols.injective
    simpa only [batchRank_succ] using hr

theorem rectangular_polynomial_power_rank {K : Type*} [Field K] [CharZero K]
    {a b c L r d D : ℕ}
    (P : PolynomialApproximation (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) r d D) (t : ℕ) :
    RankAtMost (directSum (fun _ : Fin (L ^ t) =>
      matrixCoefficients (K := K) (Fin (a ^ t)) (Fin (b ^ t)) (Fin (c ^ t))))
      ((D * t + 1) * r ^ t) :=
  rectangular_directSum_power_rank (P.rank_power t)

theorem rectangular_directSum_cyclic_rank
    {K ι A B C : Type*} [CommSemiring K]
    [DecidableEq ι] [DecidableEq A] [DecidableEq B] [DecidableEq C] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r) :
    RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) B C A)) r := by
  rcases h with ⟨a, b, c, heq⟩
  refine ⟨b, c, a, ?_⟩
  funext x y z
  have hcyc : directSum (fun _ : ι => matrixCoefficients (K := K) B C A) x y z =
      directSum (fun _ : ι => matrixCoefficients (K := K) A B C) z x y := by
    have htags : (x.1 = y.1 ∧ x.1 = z.1) ↔ (z.1 = x.1 ∧ z.1 = y.1) := by
      constructor
      · rintro ⟨hxy, hxz⟩
        exact ⟨hxz.symm, hxz.symm.trans hxy⟩
      · rintro ⟨hzx, hzy⟩
        exact ⟨hzx.symm.trans hzy, hzx.symm⟩
    simp only [directSum, htags]
    split_ifs
    · exact (matrixCoefficients_cyclic (K := K) x.2 y.2 z.2).symm
    · rfl
  rw [hcyc, congrFun (congrFun (congrFun heq z) x) y]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

theorem rectangular_directSum_rank_lower {K : Type*} [Field K]
    {a b L r : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : RankAtMost (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin a))) r) :
    L * a ^ 2 ≤ r ∧ L * (a * b) ≤ r := by
  let : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  let : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  constructor
  · simpa only [Fintype.card_fin, pow_two] using
      directSum_matrixCoefficients_rank_lower h
  · simpa only [Fintype.card_fin] using
      directSum_matrixCoefficients_rank_lower (rectangular_directSum_cyclic_rank h)

end Tensor
end MatrixMultiplication

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section ConstantRestriction

variable {F X Y Z X' Y' Z' : Type*} [CommSemiring F]
variable [Fintype X] [Fintype Y] [Fintype Z]

def restrictPolynomial (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) (P : Tensor (Polynomial F) X Y Z) :
    Tensor (Polynomial F) X' Y' Z' :=
  restrict (fun x' x => Polynomial.C (A x' x))
    (fun y' y => Polynomial.C (B y' y))
    (fun z' z => Polynomial.C (C z' z)) P

@[simp] theorem restrictPolynomial_coeff (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) (P : Tensor (Polynomial F) X Y Z) (k : ℕ)
    (x' : X') (y' : Y') (z' : Z') :
    (restrictPolynomial A B C P x' y' z').coeff k =
      restrict A B C (fun x y z => (P x y z).coeff k) x' y' z' := by
  simp only [restrictPolynomial, restrict, Polynomial.finsetSum_coeff,
    mul_assoc, Polynomial.coeff_C_mul]

theorem RankAtMost.restrictPolynomial {P : Tensor (Polynomial F) X Y Z} {r : ℕ}
    (hP : RankAtMost P r) (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) : RankAtMost (restrictPolynomial A B C P) r :=
  hP.restrict (fun x' x => Polynomial.C (A x' x))
    (fun y' y => Polynomial.C (B y' y))
    (fun z' z => Polynomial.C (C z' z))

theorem restrictPolynomial_degree_le (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) (P : Tensor (Polynomial F) X Y Z) (D : ℕ)
    (hdegree : ∀ x y z, (P x y z).degree ≤ D)
    (x' : X') (y' : Y') (z' : Z') :
    (restrictPolynomial A B C P x' y' z').degree ≤ D := by
  apply (Polynomial.degree_le_iff_coeff_zero _ _).2
  intro k hk
  rw [restrictPolynomial_coeff]
  have hzero (x : X) (y : Y) (z : Z) : (P x y z).coeff k = 0 :=
    (Polynomial.degree_le_iff_coeff_zero _ _).1 (hdegree x y z) k hk
  simp only [restrict, hzero, mul_zero, Finset.sum_const_zero]

end ConstantRestriction

namespace PolynomialApproximation

variable {F X Y Z X' Y' Z' : Type*} [Field F]

def ofRankAtMost (T : Tensor F X Y Z) (r : ℕ) (hT : RankAtMost T r) :
    PolynomialApproximation T r 0 0 where
  polynomial := fun x y z => Polynomial.C (T x y z)
  rank_bound := hT.map Polynomial.C
  vanishes := by
    intro x y z k hk
    exact (Nat.not_lt_zero k hk).elim
  leading := by
    intro x y z
    exact Polynomial.coeff_C_zero
  degree_bound := by
    intro x y z
    simpa only [Nat.cast_zero] using (Polynomial.degree_C_le (a := T x y z))

@[simp] theorem ofRankAtMost_polynomial (T : Tensor F X Y Z) (r : ℕ)
    (hT : RankAtMost T r) :
    (ofRankAtMost T r hT).polynomial = (fun x y z => Polynomial.C (T x y z)) := rfl

variable [Fintype X] [Fintype Y] [Fintype Z]
variable {T : Tensor F X Y Z} {r d D : ℕ}

def restrict (W : PolynomialApproximation T r d D)
    (A : X' → X → F) (B : Y' → Y → F) (C : Z' → Z → F) :
    PolynomialApproximation (Tensor.restrict A B C T) r d D where
  polynomial := restrictPolynomial A B C W.polynomial
  rank_bound := W.rank_bound.restrictPolynomial A B C
  vanishes := by
    intro x' y' z' k hk
    rw [restrictPolynomial_coeff]
    have hzero (x : X) (y : Y) (z : Z) : (W.polynomial x y z).coeff k = 0 :=
      W.vanishes x y z k hk
    simp only [Tensor.restrict, hzero, mul_zero, Finset.sum_const_zero]
  leading := by
    intro x' y' z'
    rw [restrictPolynomial_coeff]
    simp only [W.leading]
  degree_bound := restrictPolynomial_degree_le A B C W.polynomial D W.degree_bound

@[simp] theorem restrict_polynomial (W : PolynomialApproximation T r d D)
    (A : X' → X → F) (B : Y' → Y → F) (C : Z' → Z → F) :
    (W.restrict A B C).polynomial = restrictPolynomial A B C W.polynomial := rfl

end PolynomialApproximation

end Tensor
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

namespace Tensor

private def rectangularTagEquiv (L : ℕ) :
    Fin (L ^ 3) ≃ (Fin L × Fin L) × Fin L :=
  Fintype.equivOfCardEq (by simp [pow_succ])

private def rectangularIndexEquiv (a b c : ℕ) :
    Fin (a * b * c) ≃ Fin a × Fin b × Fin c :=
  Fintype.equivOfCardEq (by simp [mul_assoc])

theorem matrixMultiplication_directSum_symmetrized_rank {a b c L r : ℕ}
    (h : RankAtMost (directSum (fun _ : Fin L => matrixMultiplication a b c)) r) :
    RankAtMost (directSum (fun _ : Fin (L ^ 3) =>
      matrixMultiplication (a * b * c) (a * b * c) (a * b * c))) (r ^ 3) := by
  have hs := matrixCoefficients_directSum_symmetrized_rank h
  exact matrixCoefficients_directSum_rank_of_injective hs
    (rectangularTagEquiv L) (rectangularTagEquiv L).injective
    (rectangularIndexEquiv a b c) (rectangularIndexEquiv a b c).injective

private def rectangularPullback
    {FieldType SourceX SourceY SourceZ TargetX TargetY TargetZ : Type*} [Field FieldType]
    {tensor : Tensor FieldType SourceX SourceY SourceZ} {rank shift degree : ℕ}
    (witness : PolynomialApproximation tensor rank shift degree)
    (mapX : TargetX → SourceX) (mapY : TargetY → SourceY) (mapZ : TargetZ → SourceZ) :
    PolynomialApproximation (pullback mapX mapY mapZ tensor) rank shift degree where
  polynomial := pullback mapX mapY mapZ witness.polynomial
  rank_bound := witness.rank_bound.pullback mapX mapY mapZ
  vanishes := fun coordX coordY coordZ coeff bound =>
    witness.vanishes (mapX coordX) (mapY coordY) (mapZ coordZ) coeff bound
  leading := fun coordX coordY coordZ =>
    witness.leading (mapX coordX) (mapY coordY) (mapZ coordZ)
  degree_bound := fun coordX coordY coordZ =>
    witness.degree_bound (mapX coordX) (mapY coordY) (mapZ coordZ)

private def rectangularProduct
    {FieldType LeftX LeftY LeftZ RightX RightY RightZ : Type*} [Field FieldType]
    {leftTensor : Tensor FieldType LeftX LeftY LeftZ}
    {rightTensor : Tensor FieldType RightX RightY RightZ}
    {leftRank rightRank leftShift rightShift leftDegree rightDegree : ℕ}
    (left : PolynomialApproximation leftTensor leftRank leftShift leftDegree)
    (right : PolynomialApproximation rightTensor rightRank rightShift rightDegree) :
    PolynomialApproximation (product leftTensor rightTensor) (leftRank * rightRank)
      (leftShift + rightShift) (leftDegree + rightDegree) := by
  have factorization (coordX : LeftX × RightX) (coordY : LeftY × RightY)
      (coordZ : LeftZ × RightZ) :
      product left.polynomial right.polynomial coordX coordY coordZ =
        Polynomial.X ^ (leftShift + rightShift) *
          product left.normalized right.normalized coordX coordY coordZ := by
    dsimp only [product]
    rw [left.polynomial_eq, right.polynomial_eq, pow_add]
    ring
  exact {
    polynomial := product left.polynomial right.polynomial
    rank_bound := left.rank_bound.product right.rank_bound
    vanishes := by
      intro coordX coordY coordZ coeff bound
      rw [factorization]
      simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt bound, ite_false]
    leading := by
      intro coordX coordY coordZ
      rw [factorization]
      simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
        product, Polynomial.mul_coeff_zero, left.normalized_constant, right.normalized_constant]
    degree_bound := by
      intro coordX coordY coordZ
      apply Polynomial.degree_le_of_natDegree_le
      exact Polynomial.natDegree_mul_le_of_le
        (Polynomial.natDegree_le_of_degree_le (left.degree_bound coordX.1 coordY.1 coordZ.1))
        (Polynomial.natDegree_le_of_degree_le (right.degree_bound coordX.2 coordY.2 coordZ.2)) }

private def rectangularCyclic
    {FieldType CoordX CoordY CoordZ : Type*} [Field FieldType]
    {tensor : Tensor FieldType CoordX CoordY CoordZ} {rank shift degree : ℕ}
    (witness : PolynomialApproximation tensor rank shift degree) :
    PolynomialApproximation (cyclic tensor) rank shift degree where
  polynomial := cyclic witness.polynomial
  rank_bound := witness.rank_bound.cyclic
  vanishes := fun coordY coordZ coordX coeff bound =>
    witness.vanishes coordX coordY coordZ coeff bound
  leading := fun coordY coordZ coordX => witness.leading coordX coordY coordZ
  degree_bound := fun coordY coordZ coordX => witness.degree_bound coordX coordY coordZ

def PolynomialApproximation.matrixCoefficients_directSum_of_injective
    {F ι κ A B : Type*} [Field F]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq A] [DecidableEq B] {r d D : ℕ}
    (P : PolynomialApproximation
      (directSum (fun _ : ι => matrixCoefficients (K := F) A A A)) r d D)
    (f : κ → ι) (hf : Function.Injective f) (g : B → A) (hg : Function.Injective g) :
    PolynomialApproximation
      (directSum (fun _ : κ => matrixCoefficients (K := F) B B B)) r d D := by
  let coord : κ × (B × B) → ι × (A × A) :=
    fun x => (f x.1, (g x.2.1, g x.2.2))
  have heq : Tensor.pullback coord coord coord
      (directSum (fun _ : ι => matrixCoefficients (K := F) A A A)) =
      directSum (fun _ : κ => matrixCoefficients (K := F) B B B) := by
    funext x y z
    simp only [Tensor.pullback, coord, directSum, matrixCoefficients, hf.eq_iff, hg.eq_iff]
  rw [← heq]
  exact rectangularPullback P coord coord coord

def PolynomialApproximation.matrixMultiplication_directSum_symmetrized
    {a b c L r d D : ℕ}
    (P : PolynomialApproximation
      (directSum (fun _ : Fin L => matrixMultiplication a b c)) r d D) :
    PolynomialApproximation (directSum (fun _ : Fin (L ^ 3) =>
      matrixMultiplication (a * b * c) (a * b * c) (a * b * c)))
      (r ^ 3) (3 * d) (3 * D) := by
  have combine {LeftTag RightTag LeftX LeftY LeftZ RightX RightY RightZ : Type}
      [DecidableEq LeftTag] [DecidableEq RightTag]
      {leftTensor : LeftTag → Tensor ℂ LeftX LeftY LeftZ}
      {rightTensor : RightTag → Tensor ℂ RightX RightY RightZ}
      {leftRank rightRank leftShift rightShift leftDegree rightDegree : ℕ}
      (left : PolynomialApproximation (directSum leftTensor) leftRank leftShift leftDegree)
      (right : PolynomialApproximation (directSum rightTensor) rightRank rightShift rightDegree) :
      PolynomialApproximation
        (directSum (fun tag : LeftTag × RightTag => product (leftTensor tag.1) (rightTensor tag.2)))
        (leftRank * rightRank) (leftShift + rightShift) (leftDegree + rightDegree) := by
    have combined := rectangularPullback (rectangularProduct left right)
      (directSumProductEquiv LeftTag RightTag LeftX RightX)
      (directSumProductEquiv LeftTag RightTag LeftY RightY)
      (directSumProductEquiv LeftTag RightTag LeftZ RightZ)
    simpa only [directSum_product] using combined
  have base : PolynomialApproximation
      (directSum (fun _ : Fin L => matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c)))
      r d D := P
  have rotated : PolynomialApproximation
      (directSum (fun _ : Fin L => matrixCoefficients (K := ℂ) (Fin b) (Fin c) (Fin a)))
      r d D := by
    simpa only [cyclic_directSum, cyclic_matrixCoefficients] using rectangularCyclic base
  have twiceRotated : PolynomialApproximation
      (directSum (fun _ : Fin L => matrixCoefficients (K := ℂ) (Fin c) (Fin a) (Fin b)))
      r d D := by
    simpa only [cyclic_directSum, cyclic_matrixCoefficients] using rectangularCyclic rotated
  let squareIndex := Fin a × Fin b × Fin c
  let tagIndex := (Fin L × Fin L) × Fin L
  have symmetrized := rectangularPullback (combine (combine base rotated) twiceRotated)
    (fun coord : tagIndex × (squareIndex × squareIndex) =>
      (coord.1, rectangularSquareX (Fin a) (Fin b) (Fin c) coord.2))
    (fun coord : tagIndex × (squareIndex × squareIndex) =>
      (coord.1, rectangularSquareY (Fin a) (Fin b) (Fin c) coord.2))
    (fun coord : tagIndex × (squareIndex × squareIndex) =>
      (coord.1, rectangularSquareZ (Fin a) (Fin b) (Fin c) coord.2))
  have shift_eq : d + d + d = 3 * d := by ring
  have degree_eq : D + D + D = 3 * D := by ring
  have squared : PolynomialApproximation
      (directSum (fun _ : tagIndex => matrixCoefficients (K := ℂ) squareIndex squareIndex squareIndex))
      (r ^ 3) (3 * d) (3 * D) := by
    simp only [directSum_pullback] at symmetrized
    simp_rw [matrixCoefficients_cyclic_product_square
      (K := ℂ) (A := Fin a) (B := Fin b) (C := Fin c)] at symmetrized
    simpa only [pow_succ, pow_zero, one_mul, shift_eq, degree_eq] using symmetrized
  exact squared.matrixCoefficients_directSum_of_injective
    (rectangularTagEquiv L) (rectangularTagEquiv L).injective
    (rectangularIndexEquiv a b c) (rectangularIndexEquiv a b c).injective

end Tensor

theorem mul_rpow_third_le_of_cube {u v w r : ℝ} (hv : 0 ≤ v) (hr : 0 ≤ r)
    (h : u ^ 3 * v ^ w ≤ r ^ 3) : u * v ^ (w / 3) ≤ r := by
  have hpow : (v ^ (w / 3)) ^ (3 : ℕ) = v ^ w := by
    rw [← Real.rpow_mul_natCast hv]
    congr 1
    norm_num
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hr
  simpa only [mul_pow, hpow] using h

namespace Arithmetic

theorem equalRectangular_inequality {a b c L r : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : Tensor.RankAtMost
      (Tensor.directSum (fun _ : Fin L => Tensor.matrixMultiplication a b c)) r) :
    (L : ℝ) * ((a * b * c : ℕ) : ℝ) ^ (omega / 3) ≤ (r : ℝ) := by
  have hv : 1 ≤ a * b * c := Nat.mul_pos (Nat.mul_pos ha hb) hc
  have hs := equalSummand_inequality hv
    (Tensor.matrixMultiplication_directSum_symmetrized_rank h)
  apply mul_rpow_third_le_of_cube (Nat.cast_nonneg (a * b * c)) (Nat.cast_nonneg r)
  simpa only [Nat.cast_pow] using hs

theorem equalRectangular_inequality_of_polynomialApproximation
    {a b c L r d D : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (P : Tensor.PolynomialApproximation
      (Tensor.directSum (fun _ : Fin L => Tensor.matrixMultiplication a b c)) r d D) :
    (L : ℝ) * ((a * b * c : ℕ) : ℝ) ^ (omega / 3) ≤ (r : ℝ) := by
  have hv : 1 ≤ a * b * c := Nat.mul_pos (Nat.mul_pos ha hb) hc
  have hs := equalSummand_inequality_of_polynomialApproximation hv
    P.matrixMultiplication_directSum_symmetrized
  apply mul_rpow_third_le_of_cube (Nat.cast_nonneg (a * b * c)) (Nat.cast_nonneg r)
  simpa only [Nat.cast_pow] using hs

end Arithmetic

end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

end OAI
