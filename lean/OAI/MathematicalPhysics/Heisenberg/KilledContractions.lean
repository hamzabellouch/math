import OAI.MathematicalPhysics.Heisenberg.LayerEnergy

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.MeshPair
open scoped RealInnerProductSpace Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def killedPermutation (I : Set V) (σ : Equiv.Perm V) (v : EuclideanSpace ℝ V) :
    EuclideanSpace ℝ V := WithLp.toLp 2 (fun i => if i ∈ I then v.ofLp (σ.symm i) else 0)

def killedCoin (I : Set V) (a b : V) (t : ℝ) (v : EuclideanSpace ℝ V) :
    EuclideanSpace ℝ V := (1-t/2) • v + (t/2) • killedPermutation I (Equiv.swap a b) v

lemma killedCoin_generator (I : Set V) {a b : V} (hab : a ≠ b) (t : ℝ)
    (v : EuclideanSpace ℝ V) (hv : ∀ i ∉ I, v.ofLp i = 0) :
    killedCoin I a b t v = (1+t • generator (edgeVector I a b)) v := by
  ext i
  simp only [killedCoin,killedPermutation,PiLp.add_apply,PiLp.smul_apply,
    smul_eq_mul,_root_.add_apply,one_apply_eq_self,
    _root_.smul_apply,generator_apply]
  simp only [edge_inner]
  simp only [edgeVector,PiLp.sub_apply,PiLp.single_apply,Equiv.symm_swap]
  by_cases hi : i = a
  · subst i
    rw [Equiv.swap_apply_left]
    by_cases ha : a ∈ I <;> by_cases hb : b ∈ I <;> simp [ha,hb,hab,hv] <;> ring
  · by_cases hi' : i = b
    · subst i
      rw [Equiv.swap_apply_right]
      by_cases ha : a ∈ I <;> by_cases hb : b ∈ I <;> simp [ha,hb,Ne.symm hab,hv] <;> ring
    · rw [Equiv.swap_apply_of_ne_of_ne hi hi']
      by_cases hI : i ∈ I <;> simp [hi,hi',hI,hv]
      ring

omit [Fintype V] in
lemma killedCoin_support (I : Set V) (a b : V) (t : ℝ) (v : EuclideanSpace ℝ V)
    (hv : ∀ i ∉ I, v.ofLp i = 0) :
    ∀ i ∉ I, (killedCoin I a b t v).ofLp i = 0 := by
  intro i hi
  simp [killedCoin,killedPermutation,hi,hv i hi]

lemma killedCoin_bound (I : Set V) {a b : V} (hab : a ≠ b) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (v : EuclideanSpace ℝ V)
    (hv : ∀ i ∉ I, v.ofLp i = 0) : ‖killedCoin I a b t v‖ ≤ ‖v‖ := by
  rw [killedCoin_generator I hab t v hv]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (step_contraction _ (edge_norm I hab) ht ht1))

def killedSweep (I : Set V) (a b : ℕ → V) (t : ℝ) : ℕ → EuclideanSpace ℝ V → EuclideanSpace ℝ V
  | 0, v => v
  | n+1, v => killedCoin I (a n) (b n) t (killedSweep I a b t n v)

omit [Fintype V] in
lemma killedSweep_support (I : Set V) (a b : ℕ → V) (t : ℝ) (n : ℕ)
    (v : EuclideanSpace ℝ V) (hv : ∀ i ∉ I, v.ofLp i = 0) :
    ∀ i ∉ I, (killedSweep I a b t n v).ofLp i = 0 := by
  induction n with
  | zero => exact hv
  | succ n ih => exact killedCoin_support I (a n) (b n) t _ ih

lemma killedSweep_eq (I : Set V) (a b : ℕ → V) (n : ℕ)
    (hab : ∀ i<n, a i ≠ b i) (t : ℝ) (v : EuclideanSpace ℝ V)
    (hv : ∀ i ∉ I, v.ofLp i = 0) :
    killedSweep I a b t n v =
      MeshEnergy.sweep (fun i => generator (edgeVector I (a i) (b i))) n t v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [killedSweep,killedCoin_generator I (hab n (by omega)) t _
      (killedSweep_support I a b t n v hv),ih (fun i hi => hab i (by omega))]
    rfl

theorem killedSweep_energy (I : Set V) (a b : ℕ → V) (n : ℕ)
    (hab : ∀ i<n, a i ≠ b i) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ v : EuclideanSpace ℝ V, (∀ i ∉ I, v.ofLp i = 0) →
      |‖killedSweep I a b t n v‖^2 - ‖v‖^2 +
        t * ∑ i ∈ Finset.range n, (v.ofLp (a i)-v.ofLp (b i))^2| ≤ ε*|t| * ‖v‖^2 := by
  filter_upwards [sweep_energy I a b n hε] with t ht
  intro v hv
  rw [killedSweep_eq I a b n hab t v hv]
  have he : ∀ i, (if i ∈ I then v.ofLp i else 0) = v.ofLp i := by
    intro i
    split_ifs with hi
    · rfl
    · exact (hv i hi).symm
  simpa only [he] using ht v

end Heisenberg.MeshPair

namespace Heisenberg.MatrixContraction

variable {V : Type*} [Fintype V]

structure DoublySubstochastic (U : Matrix V V ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ U i j
  row : ∀ i, ∑ j, U i j ≤ 1
  col : ∀ j, ∑ i, U i j ≤ 1

lemma DoublySubstochastic.transpose {U : Matrix V V ℝ} (hU : DoublySubstochastic U) :
    DoublySubstochastic U.transpose := ⟨fun i j => hU.nonneg j i, hU.col, hU.row⟩

lemma DoublySubstochastic.mul {U W : Matrix V V ℝ}
    (hU : DoublySubstochastic U) (hW : DoublySubstochastic W) :
    DoublySubstochastic (U * W) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hU.nonneg i k) (hW.nonneg k j))
  · intro i
    change (∑ j, ∑ k, U i k * W k j) ≤ 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    exact (Finset.sum_le_sum (fun k _ =>
      mul_le_of_le_one_right (hU.nonneg i k) (hW.row k))).trans (hU.row i)
  · intro j
    change (∑ i, ∑ k, U i k * W k j) ≤ 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    exact (Finset.sum_le_sum (fun k _ =>
      mul_le_of_le_one_left (hW.nonneg k j) (hU.col k))).trans (hW.col j)

lemma weighted_square (w f : V → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * f i) ^ 2 ≤ (∑ i, w i) * ∑ i, w i * f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * f i)
  simpa only [← mul_assoc, Real.mul_self_sqrt (hw _), mul_pow,
    Real.sq_sqrt (hw _)] using h

theorem contraction {U : Matrix V V ℝ} (hU : DoublySubstochastic U) (f : V → ℝ) :
    ∑ i, ((U.mulVec f) i) ^ 2 ≤ ∑ i, (f i) ^ 2 := by
  calc
    _ ≤ ∑ i, (∑ j, U i j) * (∑ j, U i j * f j ^ 2) := by
      exact Finset.sum_le_sum (fun i _ => weighted_square (U i) f (hU.nonneg i))
    _ ≤ ∑ i, ∑ j, U i j * f j ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_left
        (Finset.sum_nonneg (fun j _ => mul_nonneg (hU.nonneg i j) (sq_nonneg _))) (hU.row i)
    _ = ∑ j, (∑ i, U i j) * f j ^ 2 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_of_le_one_left (sq_nonneg _) (hU.col j))

theorem of_partial_permutation (p : V → Option V)
    (hp : ∀ i j a, p i = some a → p j = some a → i = j) :
    DoublySubstochastic (fun i j => if p j = some i then 1 else 0) := by
  constructor
  · intro i j; split_ifs <;> norm_num
  · intro i
    have hc : (Finset.univ.filter fun j => p j = some i).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj k hk
      exact hp j k i (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
    simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      Nat.cast_le_one] using (show ((Finset.univ.filter fun j => p j = some i).card : ℝ) ≤ 1 by
        exact_mod_cast hc)
  · intro j
    cases hj : p j with
    | none => simp
    | some i => simp

theorem weighted_average {I : Type*} [Fintype I] (w : I → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (U : I → Matrix V V ℝ)
    (hU : ∀ a, DoublySubstochastic (U a)) :
    DoublySubstochastic (fun i j => ∑ a, w a * U a i j) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) ((hU a).nonneg i j))
  · intro i
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ a, w a := Finset.sum_le_sum (fun a _ =>
        mul_le_of_le_one_right (hw a) ((hU a).row i))
      _ = 1 := hs
  · intro j
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ a, w a := Finset.sum_le_sum (fun a _ =>
        mul_le_of_le_one_right (hw a) ((hU a).col j))
      _ = 1 := hs

def squareNorm (f : V → ℝ) : ℝ := ∑ i, f i ^ 2

def dot (f g : V → ℝ) : ℝ := ∑ i, f i * g i

lemma dot_half (f g : V → ℝ) :
    2 * dot f g ≤ squareNorm f + squareNorm g := by
  have h : 0 ≤ ∑ i, (f i - g i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have he : (∑ i, (f i - g i) ^ 2) = squareNorm f + squareNorm g - 2 * dot f g := by
    unfold squareNorm dot
    simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    ring_nf
  linarith

lemma dot_transpose (B : Matrix V V ℝ) (f g : V → ℝ) :
    dot f (B.mulVec g) = dot (B.transpose.mulVec f) g := by
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem two_ends (A M B : Matrix V V ℝ) (hM : DoublySubstochastic M) (f : V → ℝ) :
    squareNorm f - dot f ((B * M * A).mulVec f) ≥
      ((squareNorm f - squareNorm (A.mulVec f)) +
       (squareNorm f - squareNorm (B.transpose.mulVec f))) / 2 := by
  have he : (B * M * A).mulVec f = B.mulVec (M.mulVec (A.mulVec f)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [he, dot_transpose]
  have h := dot_half (B.transpose.mulVec f) (M.mulVec (A.mulVec f))
  have hc := contraction hM (A.mulVec f)
  change squareNorm (M.mulVec (A.mulVec f)) ≤ squareNorm (A.mulVec f) at hc
  linarith

end Heisenberg.MatrixContraction

namespace Heisenberg.MeshPair
open Heisenberg.MatrixContraction Matrix
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def killedMatrix (D : Set V) (σ : Equiv.Perm V) : Matrix V V ℝ := fun i j =>
  if j ∈ D ∧ σ j ∈ D then if i=σ j then 1 else 0 else 0

lemma killedMatrix_substochastic (D : Set V) (σ : Equiv.Perm V) :
    DoublySubstochastic (killedMatrix D σ) := by
  classical
  have h := of_partial_permutation (fun j => if j ∈ D ∧ σ j ∈ D then some (σ j) else none) (by
    intro i j a hi hj
    split_ifs at hi hj with hiD hjD
    exact σ.injective ((Option.some.inj hi).trans (Option.some.inj hj).symm))
  have he : killedMatrix D σ = (fun i j => if (if j ∈ D ∧ σ j ∈ D then some (σ j) else none) = some i then (1:ℝ) else 0) := by
    ext i j
    simp only [killedMatrix]
    split_ifs <;> simp_all [eq_comm]
  rw [he]
  convert h using 1
  apply Iff.of_eq
  apply congrArg DoublySubstochastic
  funext i j
  split_ifs <;> rfl

def residualMatrix (D : Set V) (R : Prop) (c : Bool) (a b : V) (p : ℝ) : Matrix V V ℝ :=
  if R then killedMatrix D (if c then Equiv.swap a b else 1)
  else (1-p) • killedMatrix D 1 + p • killedMatrix D (Equiv.swap a b)

lemma residualMatrix_substochastic (D : Set V) (R : Prop) (c : Bool)
    (a b : V) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    DoublySubstochastic (residualMatrix D R c a b p) := by
  by_cases hR : R
  · simp only [residualMatrix,ite_eq_left hR]
    apply killedMatrix_substochastic
  · simp only [residualMatrix,ite_eq_right hR]
    have h := weighted_average (fun z : Bool => if z then p else 1-p)
      (by intro z; cases z <;> simp <;> linarith)
      (by simp) (fun z => killedMatrix D (if z then Equiv.swap a b else 1))
      (fun _ => killedMatrix_substochastic _ _)
    have he : (1-p) • killedMatrix D 1 + p • killedMatrix D (Equiv.swap a b) =
        (fun i j => ∑ z : Bool,(if z then p else 1-p)*killedMatrix D (if z then Equiv.swap a b else 1) i j) := by
      ext i j
      simp [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_comm]
    rw [he]
    exact h

def euclideanMap (K : Matrix V V ℝ) : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V where
  toFun v := WithLp.toLp 2 (K *ᵥ v.ofLp)
  map_add' v w := by ext i; simp [Matrix.mulVec_add]
  map_smul' r v := by ext i; simp [Matrix.mulVec_smul]

omit [DecidableEq V] in
@[simp] lemma euclideanMap_apply (K : Matrix V V ℝ) (v : EuclideanSpace ℝ V) (i : V) :
    (euclideanMap K v).ofLp i=(K *ᵥ v.ofLp) i := rfl

omit [DecidableEq V] in
lemma euclideanMap_contraction (K : Matrix V V ℝ) (hK : DoublySubstochastic K)
    (v : EuclideanSpace ℝ V) : ‖euclideanMap K v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  exact contraction hK v.ofLp

lemma killedMatrix_apply (D : Set V) (σ : Equiv.Perm V) (v : EuclideanSpace ℝ V)
    (hv : ∀ i ∉ D,v.ofLp i=0) :
    euclideanMap (killedMatrix D σ) v = killedPermutation D σ v := by
  ext i
  simp only [euclideanMap_apply,Matrix.mulVec,dotProduct,killedMatrix,killedPermutation]
  rw [Finset.sum_eq_single (σ.symm i)]
  · by_cases hi : i ∈ D <;> by_cases hj : σ.symm i ∈ D <;> simp [hi,hj,hv]
  · intro j _ hj
    have hh : i ≠ σ j := by intro he; apply hj; exact (σ.symm_apply_eq.mpr he).symm
    simp [hh]
  · simp

lemma killedMatrix_identity (D : Set V) (v : EuclideanSpace ℝ V)
    (hv : ∀ i ∉ D,v.ofLp i=0) : euclideanMap (killedMatrix D 1) v=v := by
  rw [killedMatrix_apply D 1 v hv]
  ext i
  by_cases hi : i ∈ D
  · simp only [killedPermutation,hi,ite_true]
    rfl
  · simp [killedPermutation,hi,hv]

lemma residual_quiet (H D : Set V) (a b : V) (p : ℝ)
    (v : EuclideanSpace ℝ V) (hv : ∀ i ∉ D,v.ofLp i=0) :
    euclideanMap (residualMatrix D (a ∉ H ∨ b ∉ H) false a b p) v =
      if a ∈ H ∧ b ∈ H then killedCoin D a b (2*p) v else v := by
  by_cases hh : a ∈ H ∧ b ∈ H
  · simp only [residualMatrix,show ¬(a ∉ H ∨ b ∉ H) by tauto,ite_false,ite_eq_left hh]
    have he : euclideanMap ((1-p) • killedMatrix D 1 + p • killedMatrix D (Equiv.swap a b)) v =
        (1-p) • euclideanMap (killedMatrix D 1) v + p • euclideanMap (killedMatrix D (Equiv.swap a b)) v := by
      ext i
      simp only [euclideanMap_apply,Matrix.add_mulVec,Matrix.smul_mulVec,PiLp.add_apply,
        PiLp.smul_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [he,killedMatrix_identity D v hv,killedMatrix_apply D _ v hv]
    simp [killedCoin]
  · simp only [residualMatrix,show a ∉ H ∨ b ∉ H by tauto,ite_true,Bool.false_eq_true,
      ite_false,ite_eq_right hh]
    exact killedMatrix_identity D v hv

end Heisenberg.MeshPair
end

end OAI
