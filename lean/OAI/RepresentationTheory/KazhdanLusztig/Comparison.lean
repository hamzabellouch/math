import Mathlib

namespace OAI

/-!
Reciprocal low-degree rigidity and positive elementary sheaf-transfer inequalities.
-/

section


/-! The closing algebra of the admitted main proof, source §6. These are
necessary dependencies, not a substitute (conditional or special-case) main
invariance theorem. The sheaf edge-image comparison is NOT assumed as an
instance or asserted here. -/

namespace KLInvariance.Comparison

open Polynomial

/-- A polynomial supported strictly below the middle cannot equal its
reciprocal on an open real interval. This discharges the final rigidity
step after the source's two comparison inequalities have been combined. -/
theorem low_degree_zero_of_eval_reciprocal (p : ℝ[X]) (d : ℕ)
    (hp : 2 * p.natDegree < d)
    (h : ∀ q : ℝ, 0 < q → q < 1 → p.eval q = q ^ d * p.eval q⁻¹) : p = 0 := by
  have heq : p = reflect d p := by
    apply p.eq_of_infinite_eval_eq
    apply (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).mono
    intro q hq
    change p.eval q = (reflect d p).eval q
    let : Invertible q⁻¹ := invertibleOfNonzero (inv_ne_zero (ne_of_gt hq.1))
    have hr := eval₂_reflect_mul_pow (RingHom.id ℝ) q⁻¹ d p (by omega)
    simp only [eval₂_id, invOf_eq_inv, inv_inv] at hr
    have hr' := congrArg (fun z : ℝ => z * q ^ d) hr
    have hq0 : q ≠ 0 := ne_of_gt hq.1
    simp only [mul_assoc, ← mul_pow, inv_mul_cancel₀ hq0, one_pow, mul_one] at hr'
    calc
      p.eval q = q ^ d * p.eval q⁻¹ := h q hq.1 hq.2
      _ = (reflect d p).eval q := by
        simpa only [mul_comm] using hr'.symm
  by_contra hp0
  have hc := congrArg (fun f : ℝ[X] => f.coeff p.natDegree) heq.symm
  rw [coeff_reflect, revAt_le (by omega), coeff_eq_zero_of_natDegree_lt (by omega),
    coeff_natDegree] at hc
  exact (leadingCoeff_ne_zero.mpr hp0) hc.symm

/-- The exact polynomial conclusion from reciprocal difference equality,
without assuming positivity of KL coefficients. -/
theorem eq_of_eval_difference_reciprocal (p p' : ℤ[X]) (d : ℕ)
    (hp : 2 * p.natDegree < d) (hp' : 2 * p'.natDegree < d)
    (h : ∀ q : ℝ, 0 < q → q < 1 →
      p.eval₂ (Int.castRingHom ℝ) q - p'.eval₂ (Int.castRingHom ℝ) q =
      q ^ d * (p.eval₂ (Int.castRingHom ℝ) q⁻¹ -
        p'.eval₂ (Int.castRingHom ℝ) q⁻¹)) : p = p' := by
  apply sub_eq_zero.mp
  apply Polynomial.map_injective (f := Int.castRingHom ℝ) Int.cast_injective
  rw [Polynomial.map_zero]
  apply low_degree_zero_of_eval_reciprocal ((p - p').map (Int.castRingHom ℝ)) d
  · have hdeg := Polynomial.natDegree_map_le (f := Int.castRingHom ℝ) (p := p - p')
    have hsub := Polynomial.natDegree_sub_le p p'
    omega
  · intro q hq hq'
    simpa only [eval_map, eval₂_sub] using h q hq hq'

section Schedule

variable {V : Type*}

noncomputable local instance : DecidableEq V := Classical.decEq V

/-- The genuine elementary transfer `id + T E_xy` from the source's edge
schedule, expressed on vectors rather than with a choice of enumeration. -/
noncomputable def transfer (T : ℝ) (x y : V) (v : V → ℝ) : V → ℝ :=
  fun z => v z + if z = x then T * v y else 0

theorem transfer_monotone (T : ℝ) (hT : 0 ≤ T) (x y : V) :
    Monotone (transfer T x y) := by
  intro v w hv z
  dsimp [transfer]
  split_ifs
  · exact add_le_add (hv z) (mul_le_mul_of_nonneg_left (hv y) hT)
  · simpa using hv z

theorem transfer_injective (T : ℝ) (x y : V) (hxy : x ≠ y) :
    Function.Injective (transfer T x y) := by
  intro v w h
  have hy := congrFun h y
  simp only [transfer, Ne.symm hxy, ite_false, add_zero] at hy
  funext z
  have hz := congrFun h z
  dsimp [transfer] at hz
  split_ifs at hz with hz'
  · rw [hy] at hz
    exact add_right_cancel hz
  · exact add_right_cancel hz

noncomputable def idealState (T : ℝ) (edges : ℕ → V × V) (initial : V → ℝ) :
    ℕ → V → ℝ
  | 0 => initial
  | n + 1 => transfer T (edges n).1 (edges n).2 (idealState T edges initial n)

/-- Propagation of the actual Hilbert-series bound through all earlier edges.
No freeness or positivity of the *vectors* is needed for this part. -/
theorem state_le_ideal (T : ℝ) (hT : 0 ≤ T) (edges : ℕ → V × V)
    (D : ℕ → V → ℝ) (n : ℕ)
    (hstep : ∀ k < n, D (k + 1) ≤ transfer T (edges k).1 (edges k).2 (D k)) :
    D n ≤ idealState T edges (D 0) n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact (hstep n (Nat.lt_succ_self n)).trans
      (transfer_monotone T hT _ _ (ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))))

/-- Endpoint equality forces every edge-image deficit to vanish, including
those invisible in codimension one. This uses actual inequalities and the
injectivity of elementary edge transfers; it does not assume image equality.
It is the no-deficit conclusion of source (6.8). -/
theorem every_step_eq_of_endpoint_eq (T : ℝ) (hT : 0 ≤ T)
    (edges : ℕ → V × V) (D : ℕ → V → ℝ) (n : ℕ)
    (hedges : ∀ k < n, (edges k).1 ≠ (edges k).2)
    (hstep : ∀ k < n, D (k + 1) ≤ transfer T (edges k).1 (edges k).2 (D k))
    (hend : D n = idealState T edges (D 0) n) :
    ∀ k < n, D (k + 1) = transfer T (edges k).1 (edges k).2 (D k) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hD : D n ≤ idealState T edges (D 0) n :=
      state_le_ideal T hT edges D n (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
    have ht := transfer_monotone T hT (edges n).1 (edges n).2 hD
    have hlast : D (n + 1) = transfer T (edges n).1 (edges n).2 (D n) := by
      apply le_antisymm (hstep n (Nat.lt_succ_self n))
      exact ht.trans_eq hend.symm
    have heqn : D n = idealState T edges (D 0) n := by
      apply transfer_injective T (edges n).1 (edges n).2
        (hedges n (Nat.lt_succ_self n))
      exact hlast.symm.trans hend
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih (fun j hj => hedges j (Nat.lt_succ_of_lt hj))
        (fun j hj => hstep j (Nat.lt_succ_of_lt hj)) heqn k hk
    · exact hlast

end Schedule
end KLInvariance.Comparison

end

end OAI
