import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.TraceInterpolation

namespace OAI

noncomputable section

section

open scoped BigOperators Matrix.Norms.L2Operator
open Complex

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_mul_diagonal_le (A : M ι) (d : ι → ℝ)
    (hA : ‖A‖ ≤ 1) (hd : ∀ i, 0 ≤ d i) :
    ‖Matrix.trace (A * Matrix.diagonal (fun i => (d i : ℂ)))‖ ≤ ∑ i, d i := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_diagonal]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd i)]
  exact mul_le_of_le_one_left (hd i) ((entry_norm_le A i i).trans hA)

lemma trace_prod_density_le (L : List (M ι)) (A : M ι) (d : ι → ℝ)
    (hL : ∀ B ∈ L, ‖B‖ ≤ 1) (hA : ‖A‖ ≤ 1) (hd : ∀ i, 0 ≤ d i)
    (hmem : A * Matrix.diagonal (fun i => (d i : ℂ)) ∈ L) :
    ‖Matrix.trace L.prod‖ ≤ ∑ i, d i := by
  obtain ⟨l, r, rfl⟩ := List.mem_iff_append.mp hmem
  have hl : ‖l.prod‖ ≤ 1 := prod_norm_le_one l (fun B hB => hL B (by simp [hB]))
  have hr : ‖r.prod‖ ≤ 1 := prod_norm_le_one r (fun B hB => hL B (by simp [hB]))
  simp only [List.prod_append, List.prod_cons]
  rw [← mul_assoc, Matrix.trace_mul_cycle]
  rw [← mul_assoc]
  apply trace_mul_diagonal_le _ d _ hd
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
    ((norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hr).trans hl))).trans hA)

def Admissible {m : ℕ} (d : Fin m → ι → ℝ) (x : Fin m → ℝ) : Prop :=
  ∀ A : Fin m → M ι, (∀ j, ‖A j‖ ≤ 1) →
    ‖traceWord A d (fun j => (x j : ℂ))‖ ≤ 1

def exponentSet {m : ℕ} (d : Fin m → ι → ℝ) : Set (Fin m → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ Admissible d x}

lemma word_absorb_phase {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ)
    (x : Fin m → ℂ) :
    word A d x = word (fun j => A j * diagPower (d j) ((x j).im * I)) d
      (fun j => ((x j).re : ℂ)) := by
  unfold word
  congr 1
  apply List.ofFn_inj.mpr
  funext j
  have hx : x j = ((x j).im : ℂ) * I + ((x j).re : ℂ) := by
    rw [add_comm]; exact (Complex.re_add_im (x j)).symm
  calc
    A j * diagPower (d j) (x j) = A j *
        diagPower (d j) (((x j).im : ℂ) * I + ((x j).re : ℂ)) := by rw [← hx]
    _ = _ := by rw [diagPower_add, mul_assoc]

lemma admissible_complex {m : ℕ} (d : Fin m → ι → ℝ) (x : Fin m → ℝ)
    (hx : Admissible d x) (A : Fin m → M ι) (hA : ∀ j, ‖A j‖ ≤ 1)
    (z : Fin m → ℂ) (hz : ∀ j, (z j).re = x j) : ‖traceWord A d z‖ ≤ 1 := by
  unfold traceWord
  rw [word_absorb_phase]
  simp only [hz]
  apply hx
  intro j
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hA j)).trans
    (diagPower_imag_norm_le_one _ _))

lemma vertex_mem_exponentSet {m : ℕ} (d : Fin m → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hs : ∀ j, ∑ i, d j i = 1) (j : Fin m) :
    Pi.single j 1 ∈ exponentSet d := by
  have hd1 : ∀ j i, d j i ≤ 1 := by
    intro j i
    rw [← hs j]
    exact Finset.single_le_sum (fun i _ => hd j i) (Finset.mem_univ i)
  constructor
  · intro i; simp only [Pi.single_apply]; split_ifs <;> norm_num
  · intro A hA
    have hv0 : ∀ i : Fin m, 0 ≤ (((Pi.single j 1 : Fin m → ℝ) i) : ℂ).re := by
      intro i; simp only [ofReal_re, Pi.single_apply]; split_ifs <;> norm_num
    have hmem : A j * Matrix.diagonal (fun i => (d j i : ℂ)) ∈
        List.ofFn (fun k => A k * diagPower (d k) (((Pi.single j 1 : Fin m → ℝ) k) : ℂ)) := by
      apply List.mem_ofFn.mpr
      refine ⟨j, ?_⟩
      simp [diagPower_one _ (hd j)]
    have hlist : ∀ B ∈ List.ofFn (fun k => A k *
        diagPower (d k) (((Pi.single j 1 : Fin m → ℝ) k) : ℂ)), ‖B‖ ≤ 1 := by
      intro B hB
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hB
      exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hA k)).trans
        (diagPower_norm_le_one _ (hd k) (hd1 k) (hv0 k)))
    unfold traceWord word
    exact (trace_prod_density_le _ _ (d j) hlist (hA j) (hd j) hmem).trans_eq (hs j)

lemma convex_exponentSet {m : ℕ} (d : Fin m → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hd1 : ∀ j i, d j i ≤ 1) :
    Convex ℝ (exponentSet d) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro j
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
  · intro A hA
    let e (j : Fin m) (z : ℂ) := (1-z) * (x j : ℂ) + z * (y j : ℂ)
    let f (z : ℂ) := traceWord A d (fun j => e j z)
    have he : ∀ j, Differentiable ℂ (e j) := fun j =>
      (((differentiable_const (1 : ℂ)).sub differentiable_id).mul_const _).add
        (differentiable_id.mul_const _)
    have hf : Differentiable ℂ f := differentiable_traceWord A d e he
    have hre (j : Fin m) (z : ℂ) : (e j z).re = (1-z.re)*x j + z.re*y j := by
      simp [e, Complex.mul_re]
    have hbound : BddAbove ((norm ∘ f) '' HadamardThreeLines.verticalClosedStrip 0 1) := by
      refine ⟨Fintype.card ι, ?_⟩
      rintro t ⟨z, hz, rfl⟩
      have hz' : 0 ≤ z.re ∧ z.re ≤ 1 := hz
      have hw : ‖word A d (fun j => e j z)‖ ≤ 1 :=
        word_norm_le_one A d _ hA hd hd1 (fun j => by
          rw [hre]
          exact add_nonneg (mul_nonneg (sub_nonneg.mpr hz'.2) (hx.1 j))
            (mul_nonneg hz'.1 (hy.1 j)))
      exact (trace_norm_le _).trans (mul_le_of_le_one_right (Nat.cast_nonneg _) hw)
    have hleft : ∀ z ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖f z‖ ≤ 1 := by
      intro z hz
      have hz' : z.re = 0 := hz
      exact admissible_complex d x hx.2 A hA _ (fun j => by rw [hre, hz']; ring)
    have hright : ∀ z ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖f z‖ ≤ 1 := by
      intro z hz
      have hz' : z.re = 1 := hz
      exact admissible_complex d y hy.2 A hA _ (fun j => by rw [hre, hz']; ring)
    have hb1 : b ≤ 1 := by linarith
    have hbi : (b : ℂ) ∈ HadamardThreeLines.verticalClosedStrip 0 1 := ⟨hb, hb1⟩
    have hthree := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      f hbi hf.diffContOnCl hbound hleft hright
    have heval : f (b : ℂ) = traceWord A d (fun j => ((a • x + b • y) j : ℂ)) := by
      change traceWord A d (fun j => e j (b : ℂ)) = _
      apply congrArg (traceWord A d)
      funext j
      dsimp only [e]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add,
        Complex.ofReal_mul]
      have ha' : (a : ℂ) = 1 - (b : ℂ) := by exact_mod_cast (show a = 1-b by linarith)
      rw [ha']
    simpa [heval] using hthree

theorem trace_diagonal_simplex {m : ℕ} (d : Fin m → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hs : ∀ j, ∑ i, d j i = 1)
    (x : Fin m → ℝ) (hx : ∀ j, 0 ≤ x j) (hsx : ∑ j, x j = 1)
    (A : Fin m → M ι) (hA : ∀ j, ‖A j‖ ≤ 1) :
    ‖traceWord A d (fun j => (x j : ℂ))‖ ≤ 1 := by
  have hd1 : ∀ j i, d j i ≤ 1 := by
    intro j i
    rw [← hs j]
    exact Finset.single_le_sum (fun i _ => hd j i) (Finset.mem_univ i)
  have hc := convex_exponentSet d hd hd1
  have hsum := hc.sum_mem (t := Finset.univ) (w := x) (z := fun j => Pi.single j (1 : ℝ))
    (fun j _ => hx j) hsx (fun j _ => vertex_mem_exponentSet d hd hs j)
  have heq : ∑ j, x j • Pi.single j (1 : ℝ) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [heq] at hsum
  exact hsum.2 A hA

end BinaryCoordinateSweeps.TraceHolder

end

open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma prod_sandwich_succ {α : Type*} [Monoid α] (n : ℕ)
    (U D V : Fin (n+1) → α) :
    (List.ofFn (fun j => U j * D j * V j)).prod =
      U 0 * D 0 * (List.ofFn (fun j : Fin n =>
        (V j.castSucc * U j.succ) * D j.succ)).prod * V (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons]
      rw [ih (fun j => U j.succ) (fun j => D j.succ) (fun j => V j.succ)]
      simp only [List.ofFn_succ, List.prod_cons, Fin.castSucc_zero, Fin.succ_zero_eq_one,
        Fin.succ_last, Fin.castSucc_succ]
      simp only [mul_assoc]

lemma trace_prod_sandwich {n : ℕ} (U D V : Fin (n+1) → M ι) :
    Matrix.trace (List.ofFn (fun j => U j * D j * V j)).prod =
      Matrix.trace (List.ofFn (Fin.cons (V (Fin.last n) * U 0 * D 0)
        (fun j : Fin n => (V j.castSucc * U j.succ) * D j.succ))).prod := by
  rw [prod_sandwich_succ, List.ofFn_succ, List.prod_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Matrix.trace_mul_comm]
  congr 1
  simp only [mul_assoc]

theorem trace_diagonal_sandwich {n : ℕ} (d : Fin (n+1) → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hs : ∀ j, ∑ i, d j i = 1)
    (x : Fin (n+1) → ℝ) (hx : ∀ j, 0 ≤ x j) (hsx : ∑ j, x j = 1)
    (U V : Fin (n+1) → M ι) (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) :
    ‖Matrix.trace (List.ofFn (fun j => U j * diagPower (d j) (x j : ℂ) * V j)).prod‖ ≤ 1 := by
  let A : Fin (n+1) → M ι := Fin.cons (V (Fin.last n) * U 0)
    (fun j : Fin n => V j.castSucc * U j.succ)
  have hA : ∀ j, ‖A j‖ ≤ 1 := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hV _)).trans (hU _))
    · exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hV _)).trans (hU _))
  have heq : Matrix.trace (List.ofFn (fun j => U j * diagPower (d j) (x j : ℂ) * V j)).prod =
      traceWord A d (fun j => (x j : ℂ)) := by
    rw [trace_prod_sandwich]
    unfold traceWord word
    congr 2
    apply List.ofFn_inj.mpr
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  rw [heq]
  exact trace_diagonal_simplex d hd hs x hx hsx A hA

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
