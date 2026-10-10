import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.PolynomialLine01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
namespace TriangularLatticeRecovery
open scoped BigOperators
noncomputable section

def circleNorm (a : ℝ) : ℝ := ‖(a : UnitAddCircle)‖

@[simp] theorem circleNorm_zero : circleNorm 0 = 0 := by simp [circleNorm]
theorem circleNorm_nonneg (a : ℝ) : 0 ≤ circleNorm a := norm_nonneg _
theorem circleNorm_sub_le (a b : ℝ) : circleNorm (a - b) ≤ circleNorm a + circleNorm b := by
  simpa only [circleNorm, AddCircle.coe_sub] using norm_sub_le (a : UnitAddCircle) (b : UnitAddCircle)

theorem circleNorm_int_mul (z : ℤ) (a : ℝ) :
    circleNorm ((z : ℝ) * a) ≤ |(z : ℝ)| * circleNorm a := by
  simpa only [circleNorm, ← zsmul_eq_mul, AddCircle.coe_zsmul, Int.norm_eq_abs] using
    norm_zsmul_le z (a : UnitAddCircle)

theorem circleNorm_nat_mul (z : ℕ) (a : ℝ) :
    circleNorm ((z : ℝ) * a) ≤ (z : ℝ) * circleNorm a := by
  simpa using circleNorm_int_mul (z : ℤ) a

theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : UnitAddCircle) = ∑ i ∈ s, (f i : UnitAddCircle) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, AddCircle.coe_add, ih]

theorem circleNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    circleNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, circleNorm (f i) := by
  simpa only [circleNorm, coe_sum] using
    norm_sum_le s (fun i => (f i : UnitAddCircle))

theorem integer_linear_bound {ι : Type*} (s : Finset ι) (z : ι → ℤ) (a : ι → ℝ) :
    circleNorm (∑ i ∈ s, (z i : ℝ) * a i) ≤ ∑ i ∈ s, |(z i : ℝ)| * circleNorm (a i) :=
  (circleNorm_sum_le s _).trans (Finset.sum_le_sum (fun i _ => circleNorm_int_mul (z i) (a i)))

section Finite
variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq E]

 
def lineValue (L : V → ℕ → E → ℤ) (a : E → ℝ) (v : V) (j : ℕ) : ℝ :=
  ∑ e, a e * (L v j e : ℝ)

omit [Fintype V] [DecidableEq E] in
theorem lineValue_scale (L : V → ℕ → E → ℤ) (a : E → ℝ) (v : V) (j : ℕ) (B : ℝ) :
    lineValue L (fun e => B * a e) v j = B * lineValue L a v j := by
  simp only [lineValue, Finset.mul_sum, mul_assoc]

theorem reconstruct_slice (deg : E → ℕ) (M : V → E → ℤ) (w : E → V → ℤ) (B : ℕ)
    (hw : ∀ e f, ∑ v, (w e v : ℝ) * (M v f : ℝ) = if e = f then (B : ℝ) else 0)
    (a : E → ℝ) (j : ℕ) (e : E) (he : deg e = j) :
    ∑ v, (w e v : ℝ) * (∑ f, (if deg f = j then a f else 0) * (M v f : ℝ)) = B * a e := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_left_comm (w e _ : ℝ) (if deg _ = j then a _ else 0), ← Finset.mul_sum, hw]
  rw [Finset.sum_eq_single e]
  · simp [he, mul_comm]
  · intro f _ hf
    simp [Ne.symm hf]
  · intro he'
    exact False.elim (he' (Finset.mem_univ e))

omit [Fintype V] [DecidableEq E] in
theorem slice_as_difference (deg : E → ℕ) (M : V → E → ℤ) (L : V → ℕ → E → ℤ)
    (hL0 : ∀ v j e, deg e < j → L v j e = 0)
    (hLM : ∀ v j e, deg e = j → L v j e = M v e)
    (a : E → ℝ) (v : V) (j : ℕ) :
    (∑ e, (if deg e = j then a e else 0) * (M v e : ℝ)) =
      lineValue L a v j - ∑ e, if j < deg e then a e * (L v j e : ℝ) else 0 := by
  classical
  rw [lineValue, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rcases lt_trichotomy (deg e) j with h | h | h
  · simp [hL0 v j e h, ne_of_lt h, not_lt_of_ge h.le]
  · simp [h, hLM v j e h]
  · simp [Ne.symm (ne_of_lt h), h]

omit [Fintype V] [DecidableEq E] in
theorem high_part_bound (deg : E → ℕ) (L : V → ℕ → E → ℤ) (X K A : ℝ)
    (hX : 0 ≤ X) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (a : E → ℝ) (v : V) (j : ℕ)
    (ha : ∀ e, j < deg e → circleNorm (a e) * X ^ deg e ≤ A)
    (hL : ∀ e, j < deg e → |(L v j e : ℝ)| * X ^ j ≤ K * X ^ deg e) :
    circleNorm (∑ e, if j < deg e then a e * (L v j e : ℝ) else 0) * X ^ j ≤
      (Fintype.card E : ℝ) * K * A := by
  classical
  calc
    _ ≤ (∑ e, circleNorm (if j < deg e then a e * (L v j e : ℝ) else 0)) * X ^ j :=
      mul_le_mul_of_nonneg_right (circleNorm_sum_le _ _) (pow_nonneg hX _)
    _ = ∑ e, circleNorm (if j < deg e then a e * (L v j e : ℝ) else 0) * X ^ j := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _e : E, K * A := by
      apply Finset.sum_le_sum
      intro e _
      by_cases he : j < deg e
      · rw [ite_eq_left he]
        calc
          _ ≤ (|(L v j e : ℝ)| * circleNorm (a e)) * X ^ j := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg hX _)
            rw [mul_comm (a e)]
            exact circleNorm_int_mul _ _
          _ = circleNorm (a e) * (|(L v j e : ℝ)| * X ^ j) := by ring
          _ ≤ circleNorm (a e) * (K * X ^ deg e) :=
            mul_le_mul_of_nonneg_left (hL e he) (circleNorm_nonneg _)
          _ = K * (circleNorm (a e) * X ^ deg e) := by ring
          _ ≤ K * A := mul_le_mul_of_nonneg_left (ha e he) hK
      · simp only [ite_eq_right he, circleNorm_zero, zero_mul]
        positivity
    _ = _ := by simp; ring

omit [Fintype V] [DecidableEq E] in
theorem slice_bound (deg : E → ℕ) (M : V → E → ℤ) (L : V → ℕ → E → ℤ)
    (hL0 : ∀ v j e, deg e < j → L v j e = 0)
    (hLM : ∀ v j e, deg e = j → L v j e = M v e)
    (X K A : ℝ) (hX : 0 ≤ X) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (a : E → ℝ) (j : ℕ)
    (ha : ∀ e, j < deg e → circleNorm (a e) * X ^ deg e ≤ A)
    (hL : ∀ v e, j < deg e → |(L v j e : ℝ)| * X ^ j ≤ K * X ^ deg e)
    (hb : ∀ v, circleNorm (lineValue L a v j) * X ^ j ≤ A) (v : V) :
    circleNorm (∑ e, (if deg e = j then a e else 0) * (M v e : ℝ)) * X ^ j ≤
      (1 + (Fintype.card E : ℝ) * K) * A := by
  rw [slice_as_difference deg M L hL0 hLM]
  calc
    _ ≤ (circleNorm (lineValue L a v j) +
          circleNorm (∑ e, if j < deg e then a e * (L v j e : ℝ) else 0)) * X ^ j :=
      mul_le_mul_of_nonneg_right (circleNorm_sub_le _ _) (pow_nonneg hX _)
    _ = circleNorm (lineValue L a v j) * X ^ j +
        circleNorm (∑ e, if j < deg e then a e * (L v j e : ℝ) else 0) * X ^ j := by ring
    _ ≤ A + (Fintype.card E : ℝ) * K * A :=
      add_le_add (hb v) (high_part_bound deg L X K A hX hK hA a v j ha (hL v))
    _ = _ := by ring

theorem recover_one (deg : E → ℕ) (M : V → E → ℤ) (L : V → ℕ → E → ℤ)
    (w : E → V → ℤ) (B : ℕ)
    (hw : ∀ e f, ∑ v, (w e v : ℝ) * (M v f : ℝ) = if e = f then (B : ℝ) else 0)
    (hL0 : ∀ v j e, deg e < j → L v j e = 0)
    (hLM : ∀ v j e, deg e = j → L v j e = M v e)
    (X K W A : ℝ) (hX : 0 ≤ X) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hwW : ∀ e, ∑ v, |(w e v : ℝ)| ≤ W)
    (a : E → ℝ) (j : ℕ)
    (ha : ∀ e, j < deg e → circleNorm (a e) * X ^ deg e ≤ A)
    (hL : ∀ v e, j < deg e → |(L v j e : ℝ)| * X ^ j ≤ K * X ^ deg e)
    (hb : ∀ v, circleNorm (lineValue L a v j) * X ^ j ≤ A)
    (e : E) (he : deg e = j) :
    circleNorm ((B : ℝ) * a e) * X ^ deg e ≤ W * (1 + (Fintype.card E : ℝ) * K) * A := by
  let f (v : V) := ∑ e, (if deg e = j then a e else 0) * (M v e : ℝ)
  have hf (v : V) : circleNorm (f v) * X ^ j ≤ (1 + (Fintype.card E : ℝ) * K) * A :=
    slice_bound deg M L hL0 hLM X K A hX hK hA a j ha hL hb v
  rw [← reconstruct_slice deg M w B hw a j e he, he]
  change circleNorm (∑ v, (w e v : ℝ) * f v) * X ^ j ≤ _
  calc
    _ ≤ (∑ v, |(w e v : ℝ)| * circleNorm (f v)) * X ^ j :=
      mul_le_mul_of_nonneg_right (integer_linear_bound _ _ _) (pow_nonneg hX _)
    _ = ∑ v, |(w e v : ℝ)| * (circleNorm (f v) * X ^ j) := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro v _; ring
    _ ≤ ∑ v, |(w e v : ℝ)| * ((1 + (Fintype.card E : ℝ) * K) * A) :=
      Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hf v) (abs_nonneg _))
    _ = (∑ v, |(w e v : ℝ)|) * ((1 + (Fintype.card E : ℝ) * K) * A) := by rw [Finset.sum_mul]
    _ ≤ W * ((1 + (Fintype.card E : ℝ) * K) * A) :=
      mul_le_mul_of_nonneg_right (hwW e) (by positivity)
    _ = _ := by ring

theorem scaled_nat_bound (B : ℕ) (a X A T : ℝ) (j : ℕ)
    (hX : 0 ≤ X) (hA : 0 ≤ A) (hBT : (B : ℝ) ≤ T)
    (ha : circleNorm a * X ^ j ≤ A) : circleNorm ((B : ℝ) * a) * X ^ j ≤ T * A := by
  calc
    _ ≤ ((B : ℝ) * circleNorm a) * X ^ j :=
      mul_le_mul_of_nonneg_right (circleNorm_nat_mul B a) (pow_nonneg hX _)
    _ = (B : ℝ) * (circleNorm a * X ^ j) := by ring
    _ ≤ (B : ℝ) * A := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)
    _ ≤ T * A := mul_le_mul_of_nonneg_right hBT hA

 
theorem recover_aux (deg : E → ℕ) (M : V → E → ℤ) (L : V → ℕ → E → ℤ)
    (w : E → V → ℤ) (B : ℕ)
    (hw : ∀ e f, ∑ v, (w e v : ℝ) * (M v f : ℝ) = if e = f then (B : ℝ) else 0)
    (hL0 : ∀ v j e, deg e < j → L v j e = 0)
    (hLM : ∀ v j e, deg e = j → L v j e = M v e)
    (X K W T : ℝ) (hX : 0 ≤ X) (hK : 0 ≤ K)
    (hwW : ∀ e, ∑ v, |(w e v : ℝ)| ≤ W)
    (hL : ∀ v j e, j < deg e → |(L v j e : ℝ)| * X ^ j ≤ K * X ^ deg e)
    (hBT : (B : ℝ) ≤ T) (hWT : W * (1 + (Fintype.card E : ℝ) * K) ≤ T)
    (k : ℕ) : ∀ (a : E → ℝ) (A : ℝ), 0 ≤ A →
    (∀ v j, 0 < j → j ≤ k → circleNorm (lineValue L a v j) * X ^ j ≤ A) →
    (∀ e, k < deg e → circleNorm (a e) * X ^ deg e ≤ A) →
    ∀ e, 0 < deg e → circleNorm ((B : ℝ) ^ k * a e) * X ^ deg e ≤ T ^ k * A := by
  have hT : 0 ≤ T := (Nat.cast_nonneg B).trans hBT
  induction k with
  | zero =>
    intro a A hA hb ha e he
    simpa using ha e he
  | succ k ih =>
    intro a A hA hb ha
    let a' (e : E) : ℝ := (B : ℝ) * a e
    have hA' : 0 ≤ T * A := mul_nonneg hT hA
    have hb' (v : V) (j : ℕ) (hj : 0 < j) (hjk : j ≤ k) :
        circleNorm (lineValue L a' v j) * X ^ j ≤ T * A := by
      dsimp only [a']
      rw [lineValue_scale]
      exact scaled_nat_bound B _ X A T j hX hA hBT (hb v j hj (by omega))
    have ha' (e : E) (he : k < deg e) : circleNorm (a' e) * X ^ deg e ≤ T * A := by
      obtain heq | hlt := eq_or_lt_of_le (Nat.succ_le_of_lt he)
      · have heq' : deg e = k + 1 := heq.symm
        exact (recover_one deg M L w B hw hL0 hLM X K W A hX hK hA hwW
          a (k + 1) ha (fun v e hh => hL v (k + 1) e hh)
          (fun v => hb v (k + 1) (by omega) le_rfl) e heq').trans
            (mul_le_mul_of_nonneg_right hWT hA)
      · exact scaled_nat_bound B (a e) X A T (deg e) hX hA hBT (ha e hlt)
    intro e he
    have hh := ih a' (T * A) hA' hb' ha' e he
    have heq : (B : ℝ) ^ (k + 1) * a e = (B : ℝ) ^ k * a' e := by
      dsimp only [a']; rw [pow_succ]; ring
    have hpow : T ^ (k + 1) * A = T ^ k * (T * A) := by rw [pow_succ]; ring
    rw [heq, hpow]
    exact hh

theorem recover (deg : E → ℕ) (d : ℕ) (hdeg : ∀ e, deg e ≤ d)
    (M : V → E → ℤ) (L : V → ℕ → E → ℤ) (w : E → V → ℤ) (B : ℕ)
    (hw : ∀ e f, ∑ v, (w e v : ℝ) * (M v f : ℝ) = if e = f then (B : ℝ) else 0)
    (hL0 : ∀ v j e, deg e < j → L v j e = 0)
    (hLM : ∀ v j e, deg e = j → L v j e = M v e)
    (X K W T : ℝ) (hX : 0 ≤ X) (hK : 0 ≤ K)
    (hwW : ∀ e, ∑ v, |(w e v : ℝ)| ≤ W)
    (hL : ∀ v j e, j < deg e → |(L v j e : ℝ)| * X ^ j ≤ K * X ^ deg e)
    (hBT : (B : ℝ) ≤ T) (hWT : W * (1 + (Fintype.card E : ℝ) * K) ≤ T)
    (a : E → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ v j, 0 < j → j ≤ d → circleNorm (lineValue L a v j) * X ^ j ≤ A) :
    ∀ e, 0 < deg e → circleNorm ((B : ℝ) ^ d * a e) * X ^ deg e ≤ T ^ d * A := by
  apply recover_aux deg M L w B hw hL0 hLM X K W T hX hK hwW hL hBT hWT d a A hA hb
  intro e he
  exact False.elim ((not_lt_of_ge (hdeg e)) he)

end Finite
end
end TriangularLatticeRecovery

namespace MultivariateCoefficientRecovery
open scoped BigOperators
open PolynomialLineCoefficients TriangularLatticeRecovery
noncomputable section

theorem recovery_constants (n d : ℕ) :
    ∃ B T : ℕ, 0 < B ∧ 0 < T ∧ ∀ N : ℕ, 0 < N →
      ∀ x : Grid n d → Fin n → ℕ, (∀ v i, x v i ≤ N) →
      ∀ a : Grid n d → ℝ, ∀ A : ℝ, 0 ≤ A →
        (∀ v : Grid n d, ∀ j : ℕ, 0 < j → j ≤ n * d →
          circleNorm ((line a (x v) (fun i => (v i).val)).coeff j) * (N : ℝ) ^ j ≤ A) →
        ∀ e : Grid n d, 0 < totalDegree e →
          circleNorm ((B : ℝ) * a e) * (N : ℝ) ^ totalDegree e ≤ (T : ℝ) * A := by
  classical
  obtain ⟨B, hB, w, hw⟩ := IntegerGridInterpolation.exists_integer_weights n d
  let K : ℕ := (d + 1) ^ (n * d)
  let W : ℕ := ∑ e : Grid n d, ∑ v : Grid n d, (w e v).natAbs
  let T : ℕ := B + W * (1 + Fintype.card (Grid n d) * K)
  have hT : 0 < T := by dsimp [T]; omega
  refine ⟨B ^ (n * d), T ^ (n * d), pow_pos hB _, pow_pos hT _, ?_⟩
  intro N hN x hx a A hA hb
  let M (v e : Grid n d) : ℤ := ∏ i, ((v i).val : ℤ) ^ (e i).val
  let L (v : Grid n d) (j : ℕ) (e : Grid n d) : ℤ :=
    (natLine e (x v) (fun i => (v i).val)).coeff j
  have hM (v e : Grid n d) : (M v e : ℝ) = ∏ i, ((v i).val : ℝ) ^ (e i).val := by
    simp only [M, Int.cast_prod, Int.cast_pow, Int.cast_natCast]
  have hw' (e f : Grid n d) : ∑ v, (w e v : ℝ) * (M v f : ℝ) =
      if e = f then (B : ℝ) else 0 := by simpa only [hM] using hw e f
  have hL0 (v : Grid n d) (j : ℕ) (e : Grid n d) (he : totalDegree e < j) : L v j e = 0 := by
    simp only [L, natLine_coeff_zero e _ _ he, Nat.cast_zero]
  have hLM (v : Grid n d) (j : ℕ) (e : Grid n d) (he : totalDegree e = j) : L v j e = M v e := by
    subst j
    simp only [L, natLine_top_coeff, Nat.cast_prod, Nat.cast_pow, M]
  have hW (e : Grid n d) : ∑ v : Grid n d, |(w e v : ℝ)| ≤ (W : ℝ) := by
    have hh : ∑ v : Grid n d, (w e v).natAbs ≤ W :=
      Finset.single_le_sum (f := fun e : Grid n d => ∑ v : Grid n d, (w e v).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    simpa only [Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs] using
      (Nat.cast_le.mpr hh : ((∑ v : Grid n d, (w e v).natAbs : ℕ) : ℝ) ≤ W)
  have hL (v : Grid n d) (j : ℕ) (e : Grid n d) (he : j < totalDegree e) :
      |(L v j e : ℝ)| * (N : ℝ) ^ j ≤ (K : ℝ) * (N : ℝ) ^ totalDegree e := by
    have hh := natLine_coeff_bound hN e (x v) (fun i => (v i).val) (hx v)
      (fun i => Nat.le_of_lt_succ (v i).isLt) he.le
    have hn : 0 ≤ (L v j e : ℝ) := by dsimp [L]; positivity
    rw [abs_of_nonneg hn]
    have heq : (N : ℝ) ^ (totalDegree e - j) * N ^ j = N ^ totalDegree e := by
      rw [← pow_add, Nat.sub_add_cancel he.le]
    calc
      _ ≤ ((d + 1 : ℝ) ^ (n * d) * N ^ (totalDegree e - j)) * N ^ j :=
        mul_le_mul_of_nonneg_right hh (by positivity)
      _ = (K : ℝ) * N ^ totalDegree e := by
        dsimp only [K]
        push_cast
        rw [mul_assoc, heq]
  have hBT : (B : ℝ) ≤ T := by exact_mod_cast (Nat.le_add_right B _)
  have hWT : (W : ℝ) * (1 + (Fintype.card (Grid n d) : ℝ) * K) ≤ T := by
    exact_mod_cast (Nat.le_add_left (W * (1 + Fintype.card (Grid n d) * K)) B)
  have hb' (v : Grid n d) (j : ℕ) (hj : 0 < j) (hjd : j ≤ n * d) :
      circleNorm (lineValue L a v j) * (N : ℝ) ^ j ≤ A := by
    have hh := hb v j hj hjd
    simpa only [line_coeff, lineValue, L, Int.cast_natCast] using hh
  have hh := recover totalDegree (n * d) totalDegree_le M L w B hw' hL0 hLM
    (N : ℝ) K W T (Nat.cast_nonneg _) (Nat.cast_nonneg _) hW hL hBT hWT a A hA hb'
  simpa only [Nat.cast_pow] using hh

end
end MultivariateCoefficientRecovery

end
end
end
end

end OAI
