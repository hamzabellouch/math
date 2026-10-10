import Mathlib

namespace OAI

namespace PiExponent.NumericalAmpleness
open Set
open scoped Topology

theorem polynomial_pos_at_left_of_margin
    (P : Polynomial ℝ) (d : ℕ) (r ε b : ℝ) (hr : 0 ≤ r) (hε : 0 < ε)
    (hrb : r < b) (hpositive : 0 < P.eval b)
    (hderivative : ∀ t : ℝ, r < t →
      (t + ε) * P.derivative.eval t ≤ (d : ℝ) * P.eval t) :
    0 < P.eval r := by
  let Q : ℝ → ℝ := fun t => P.eval t / (t+ε)^d
  have hbase (x : ℝ) (hx : x ∈ Icc r b) : 0 < x+ε := by
    have := hx.1
    linarith
  have hderiv (x : ℝ) (hx : x ∈ Icc r b) :
      HasDerivAt Q
        ((P.derivative.eval x * (x+ε)^d -
          P.eval x * ((d:ℝ) * (x+ε)^(d-1))) / ((x+ε)^d)^2) x := by
    convert! (P.hasDerivAt x).div (((hasDerivAt_id x).add_const ε).pow d)
      (pow_ne_zero d (ne_of_gt (hbase x hx))) using 1
    simp
  have hanti : AntitoneOn Q (Icc r b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc r b)
    · exact P.continuousOn.div ((continuous_id.add continuous_const).pow d).continuousOn
        (fun x hx => pow_ne_zero d (ne_of_gt (hbase x hx)))
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : r < x := (show x ∈ Ioo r b by simpa only [interior_Icc] using hx).1
      have h := hderivative x hx'
      rw [(hderiv x (interior_subset hx)).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      cases d with
      | zero =>
        simp only [Nat.cast_zero, zero_mul, pow_zero, mul_one, mul_zero, sub_zero] at h ⊢
        exact nonpos_of_mul_nonpos_left (by simpa only [mul_comm] using h)
          (hbase x (interior_subset hx))
      | succ n =>
        have he : P.derivative.eval x * (x+ε)^(n+1) -
            P.eval x * ((n+1:ℕ):ℝ) * (x+ε)^n =
            (x+ε)^n * ((x+ε)*P.derivative.eval x - ((n+1:ℕ):ℝ)*P.eval x) := by
          rw [pow_succ]
          ring
        have hn : (x+ε)^n * ((x+ε)*P.derivative.eval x -
            ((n+1:ℕ):ℝ)*P.eval x) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt (pow_pos (hbase x (interior_subset hx)) n))
            (sub_nonpos.mpr h)
        simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, ← mul_assoc, he] using hn
  have hle : Q b ≤ Q r := hanti ⟨le_rfl,hrb.le⟩ ⟨hrb.le,le_rfl⟩ hrb.le
  have hq : 0 < Q b := div_pos hpositive
    (pow_pos (by linarith) d)
  exact (div_pos_iff_of_pos_right (pow_pos (by linarith : 0 < r+ε) d)).mp (hq.trans_le hle)

theorem polynomial_pos_at_boundary_of_margin
    (P : Polynomial ℝ) (d : ℕ) (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 < ε)
    (hpositive : ∀ t : ℝ, r < t → 0 < P.eval t)
    (hderivative : ∀ t : ℝ, r < t →
      (t+ε) * P.derivative.eval t ≤ (d:ℝ) * P.eval t) : 0 < P.eval r :=
  polynomial_pos_at_left_of_margin P d r ε (r+1) hr hε (by linarith)
    (hpositive (r+1) (by linarith)) hderivative

theorem polynomial_pos_at_boundary_of_rational_margin
    (P : Polynomial ℝ) (d : ℕ) (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 < ε)
    (hpositive : ∀ t : ℚ, r < (t:ℝ) → 0 < P.eval (t:ℝ))
    (hderivative : ∀ t : ℚ, r < (t:ℝ) →
      ((t:ℝ)+ε) * P.derivative.eval (t:ℝ) ≤ (d:ℝ) * P.eval (t:ℝ)) :
    0 < P.eval r := by
  have hreal (x : ℝ) : x ≤ r ∨ (x+ε)*P.derivative.eval x ≤ (d:ℝ)*P.eval x := by
    refine DenseRange.induction_on
      (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q:ℝ))) x ?_ ?_
    · exact isClosed_le continuous_id continuous_const |>.union
        (isClosed_le ((continuous_id.add continuous_const).mul P.derivative.continuous)
          (continuous_const.mul P.continuous))
    · intro q
      by_cases hq : (q:ℝ) ≤ r
      · exact Or.inl hq
      · exact Or.inr (hderivative q (lt_of_not_ge hq))
  obtain ⟨b,hrb,hb⟩ := exists_rat_btwn (show r < r+1 by linarith)
  exact polynomial_pos_at_left_of_margin P d r ε (b:ℝ) hr hε hrb (hpositive b hrb)
    (fun x hx => (hreal x).resolve_left (not_le_of_gt hx))

theorem nonnegative_rat_nat_ratio (q : ℚ) (hq : 0 ≤ q) :
    ∃ a b : ℕ, 0 < b ∧ (q:ℝ) = (a:ℝ)/b := by
  refine ⟨q.num.natAbs,q.den,q.pos,?_⟩
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  rw [Rat.cast_def, Nat.cast_natAbs, abs_of_nonneg hn]

theorem exists_positive_rational_below_of_polynomial_pos
    (P : Polynomial ℝ) (r : ℝ) (hr : 0 < r) (hP : 0 < P.eval r) :
    ∃ q : ℚ, 0 < (q:ℝ) ∧ (q:ℝ) < r ∧ 0 < P.eval (q:ℝ) := by
  have hn : {t : ℝ | 0 < P.eval t} ∈ 𝓝 r :=
    P.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hP)
  obtain ⟨a,ha,hsub⟩ := exists_Ioc_subset_of_mem_nhds' hn hr
  obtain ⟨q,haq,hqr⟩ := exists_rat_btwn ha.2
  exact ⟨q,ha.1.trans_lt haq,hqr,hsub ⟨haq,hqr.le⟩⟩

end PiExponent.NumericalAmpleness

end OAI
