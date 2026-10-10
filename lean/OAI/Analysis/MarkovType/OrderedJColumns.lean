import OAI.Analysis.MarkovType.AlternatingNorm
import OAI.Analysis.MarkovType.SubdivisionOperators
import OAI.Analysis.MarkovType.JConvexityBasic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

private theorem range_cut_add_shift {E : Type*} [AddCommGroup E]
    (z : ℕ → E) {n r : ℕ} (hr : r ≤ n) :
    (∑ j ∈ Finset.range n, if j < r then z j else -z j) +
        (∑ j ∈ Finset.range n, z (r + j)) =
      ∑ j ∈ Finset.range r, (z j + z (n + j)) := by
  classical
  have hsplit : (∑ j ∈ Finset.range n, z j) =
      (∑ j ∈ Finset.range r, z j) +
        ∑ j ∈ Finset.range (n - r), z (r + j) := by
    simpa only [Nat.add_sub_of_le hr] using Finset.sum_range_add z r (n - r)
  have hcut : (∑ j ∈ Finset.range n, if j < r then z j else -z j) =
      (∑ j ∈ Finset.range r, z j) + (∑ j ∈ Finset.range r, z j) -
        ∑ j ∈ Finset.range n, z j := by
    conv_lhs => rw [← Nat.add_sub_of_le hr, Finset.sum_range_add]
    have hleft : (∑ j ∈ Finset.range r, if j < r then z j else -z j) =
        ∑ j ∈ Finset.range r, z j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ite_eq_left (Finset.mem_range.mp hj)]
    have hright : (∑ j ∈ Finset.range (n - r),
        if r + j < r then z (r + j) else -z (r + j)) =
        -(∑ j ∈ Finset.range (n - r), z (r + j)) := by
      have hnot (j : ℕ) : ¬ r + j < r := by omega
      simp only [hnot, ite_false, Finset.sum_neg_distrib]
    rw [hleft, hright, hsplit]
    abel
  have hcross : (∑ j ∈ Finset.range n, z j) +
        (∑ j ∈ Finset.range r, z (n + j)) =
      (∑ j ∈ Finset.range r, z j) + ∑ j ∈ Finset.range n, z (r + j) := by
    rw [← Finset.sum_range_add, ← Finset.sum_range_add, Nat.add_comm n r]
  have hshift : (∑ j ∈ Finset.range n, z (r + j)) =
      (∑ j ∈ Finset.range n, z j) + (∑ j ∈ Finset.range r, z (n + j)) -
        ∑ j ∈ Finset.range r, z j := by
    rw [hcross]
    abel
  rw [hcut, hshift, Finset.sum_add_distrib]
  abel

namespace C00

def jColumn (n m j : ℕ) : C00 :=
  ∑ t ∈ Finset.range m, (basis (2 * n * t + j) - basis (2 * n * t + n + j))

theorem jColumn_add_period (n m j : ℕ) :
    jColumn n m j + jColumn n m (n + j) = basis j - basis (2 * n * m + j) := by
  unfold jColumn
  rw [← Finset.sum_add_distrib]
  calc
    (∑ t ∈ Finset.range m,
        ((basis (2 * n * t + j) - basis (2 * n * t + n + j)) +
          (basis (2 * n * t + (n + j)) - basis (2 * n * t + n + (n + j))))) =
        ∑ t ∈ Finset.range m,
          (basis (2 * n * t + j) - basis (2 * n * (t + 1) + j)) := by
      apply Finset.sum_congr rfl
      intro t _
      have hmid : 2 * n * t + (n + j) = 2 * n * t + n + j := by omega
      have hend : 2 * n * t + n + (n + j) = 2 * n * (t + 1) + j := by ring
      rw [hmid, hend]
      abel
    _ = basis j - basis (2 * n * m + j) := by
      simpa only [Nat.mul_zero, Nat.zero_add] using
        Finset.sum_range_sub' (fun t => basis (2 * n * t + j)) m

theorem shift_jColumn (r n m j : ℕ) :
    shift r (jColumn n m j) = jColumn n m (r + j) := by
  change Finsupp.mapDomain.addMonoidHom (fun i => r + i) (jColumn n m j) = _
  rw [jColumn, map_sum]
  unfold jColumn
  apply Finset.sum_congr rfl
  intro t _
  simp only [map_sub, basis, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.mapDomain_single]
  have h1 : r + (2 * n * t + j) = 2 * n * t + (r + j) := by omega
  have h2 : r + (2 * n * t + n + j) = 2 * n * t + n + (r + j) := by omega
  rw [h1, h2]

theorem cutSum_jColumn_add_shift (n m : ℕ) (r : Fin n) :
    (∑ j : Fin n, cutSign r j • jColumn n m j.val) +
        shift r.val (∑ j ∈ Finset.range n, jColumn n m j) =
      ∑ j ∈ Finset.range r.val, (basis j - basis (2 * n * m + j)) := by
  have hcut : (∑ j : Fin n, cutSign r j • jColumn n m j.val) =
      ∑ j ∈ Finset.range n, if j < r.val then jColumn n m j else -jColumn n m j := by
    simp only [cutSign, ite_smul, one_smul, neg_one_smul]
    exact Fin.sum_univ_eq_sum_range
      (fun j => if j < r.val then jColumn n m j else -jColumn n m j) n
  have hshift : shift r.val (∑ j ∈ Finset.range n, jColumn n m j) =
      ∑ j ∈ Finset.range n, jColumn n m (r.val + j) := by
    change Finsupp.mapDomain.addMonoidHom (fun i => r.val + i) _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => shift_jColumn r.val n m j)
  rw [hcut, hshift, range_cut_add_shift (jColumn n m) r.isLt.le]
  exact Finset.sum_congr rfl (fun j _ => jColumn_add_period n m j)

theorem sum_jColumn (n m : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range n, jColumn n m j) =
      (n : ℝ) • uniformSubdivision n (alternating m) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsingle (k : ℕ) : (n : ℝ) • uniformSubdivision n (basis k) =
      ∑ j ∈ Finset.range n, basis (n * k + j) := by
    simp only [basis, uniformSubdivision_single, Finset.smul_sum,
      Finsupp.smul_single, smul_eq_mul, div_eq_mul_inv, one_mul,
      mul_inv_cancel₀ hn0]
    exact Fin.sum_univ_eq_sum_range (fun j => Finsupp.single (n * k + j) (1 : ℝ)) n
  rw [alternating, map_sum, Finset.smul_sum]
  simp only [map_sub, smul_sub, hsingle]
  simp only [jColumn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : n * (2 * t) + j = 2 * n * t + j := by ring
  have h2 : n * (2 * t + 1) + j = 2 * n * t + n + j := by ring
  rw [h1, h2]

end C00

namespace OrderedNorm

private theorem finite_sum_le (N : OrderedNorm) {A : Type*}
    (s : Finset A) (f : A → C00) : N (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (N.add_le _ _).trans (add_le_add le_rfl ih)

theorem shift_norm (N : OrderedNorm) (r : ℕ) (x : C00) : N (C00.shift r x) = N x := by
  obtain ⟨m, a, rfl⟩ := C00.exists_ofArray x
  rw [C00.shift_ofArray]
  exact N.spreading (fun i => r + i.val)
    (fun i j hij => Nat.add_lt_add_left hij r) a

theorem basis_norm (N : OrderedNorm) (i : ℕ) : N (C00.basis i) = N (C00.basis 0) := by
  simpa only [C00.shift_basis, Nat.add_zero] using N.shift_norm i (C00.basis 0)

theorem jColumn_norm (N : OrderedNorm) (n m j : ℕ) (hn : 0 < n) :
    N (C00.jColumn n m j) = N.alternatingNorm m := by
  have hp (t : Fin m) : 2 * n * t.val + j < 2 * n * t.val + n + j := by omega
  have hnext (t u : Fin m) (htu : t < u) :
      2 * n * t.val + n + j < 2 * n * u.val + j := by
    have hmul := Nat.mul_le_mul_left (2 * n) (Nat.succ_le_of_lt htu)
    rw [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hmul
    omega
  have h := N.alternatingPairs_norm (fun t : Fin m => 2 * n * t.val + j)
    (fun t => 2 * n * t.val + n + j) hp hnext
  rw [Fin.sum_univ_eq_sum_range
    (fun t => C00.basis (2 * n * t + j) - C00.basis (2 * n * t + n + j)) m] at h
  exact h

theorem jColumn_cut_lower (N : OrderedNorm)
    (hsub : ∀ q : ℕ, 0 < q → ∀ x : C00,
      N ((q : ℝ) • C00.uniformSubdivision q x) = (q : ℝ) * N x)
    (n m : ℕ) (hn : 0 < n) (r : Fin n) :
    (n : ℝ) * N.alternatingNorm m - 2 * (n : ℝ) * N (C00.basis 0) ≤
      N ((∑ j : Fin n, cutSign r j • C00.jColumn n m j.val)) := by
  let total := ∑ j ∈ Finset.range n, C00.jColumn n m j
  let err := ∑ j ∈ Finset.range r.val,
    (C00.basis j - C00.basis (2 * n * m + j))
  let cut := (∑ j : Fin n, cutSign r j • C00.jColumn n m j.val)
  have hid : cut + C00.shift r.val total = err := C00.cutSum_jColumn_add_shift n m r
  have herr : N err ≤ 2 * (n : ℝ) * N (C00.basis 0) := by
    have hpoint (j : ℕ) :
        N (C00.basis j - C00.basis (2 * n * m + j)) ≤ 2 * N (C00.basis 0) := by
      calc
        N (C00.basis j - C00.basis (2 * n * m + j)) ≤
            N (C00.basis j) + N (-(C00.basis (2 * n * m + j))) :=
          by simpa only [sub_eq_add_neg] using
            N.add_le (C00.basis j) (-(C00.basis (2 * n * m + j)))
        _ = 2 * N (C00.basis 0) := by
          rw [N.neg, N.basis_norm j, N.basis_norm (2 * n * m + j)]
          ring
    calc
      N err ≤ ∑ j ∈ Finset.range r.val,
          N (C00.basis j - C00.basis (2 * n * m + j)) := N.finite_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range r.val, 2 * N (C00.basis 0) :=
        Finset.sum_le_sum (fun j _ => hpoint j)
      _ = (r.val : ℝ) * (2 * N (C00.basis 0)) := by simp
      _ ≤ (n : ℝ) * (2 * N (C00.basis 0)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast r.isLt.le)
          (mul_nonneg (by norm_num) (N.nonneg _))
      _ = 2 * (n : ℝ) * N (C00.basis 0) := by ring
  have htotal : N total = (n : ℝ) * N.alternatingNorm m := by
    change N (∑ j ∈ Finset.range n, C00.jColumn n m j) = _
    rw [C00.sum_jColumn n m hn]
    exact hsub n hn (C00.alternating m)
  have htriangle : N total ≤ N err + N cut := by
    have hrewrite : C00.shift r.val total = err + (-cut) := by rw [← hid]; abel
    calc
      N total = N (C00.shift r.val total) := (N.shift_norm r.val total).symm
      _ = N (err + (-cut)) := congrArg N hrewrite
      _ ≤ N err + N (-cut) := N.add_le _ _
      _ = N err + N cut := by rw [N.neg]
  rw [htotal] at htriangle
  linarith

theorem exists_unit_jColumns_of_unbounded (N : OrderedNorm)
    (hsub : ∀ q : ℕ, 0 < q → ∀ x : C00,
      N ((q : ℝ) • C00.uniformSubdivision q x) = (q : ℝ) * N x)
    (hunbounded : ¬ BddAbove (Set.range N.alternatingNorm))
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : Fin n → C00, (∀ j, N (x j) = 1) ∧
      ∀ r : Fin n, (n : ℝ) * (1 - δ) < N (∑ j, cutSign r j • x j) := by
  classical
  have hex : ∃ m : ℕ, 2 * N (C00.basis 0) / δ + 1 < N.alternatingNorm m := by
    by_contra h
    push Not at h
    exact hunbounded ⟨2 * N (C00.basis 0) / δ + 1, by
      rintro _ ⟨m, rfl⟩
      exact h m⟩
  obtain ⟨m, hm⟩ := hex
  let R := N.alternatingNorm m
  have hR : 0 < R := by
    have hnonneg := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (N.nonneg (C00.basis 0))) hδ.le
    dsimp only [R]
    linarith
  have hbudget : 2 * N (C00.basis 0) < δ * R := by
    have hdiv : 2 * N (C00.basis 0) / δ < R := by dsimp [R]; linarith
    have hmul := (div_lt_iff₀ hδ).mp hdiv
    simpa only [mul_comm] using hmul
  let x : Fin n → C00 := fun j => R⁻¹ • C00.jColumn n m j.val
  refine ⟨x, ?_, ?_⟩
  · intro j
    change N (R⁻¹ • C00.jColumn n m j.val) = 1
    rw [N.smul, abs_of_pos (inv_pos.mpr hR), N.jColumn_norm n m j.val hn]
    exact inv_mul_cancel₀ hR.ne'
  · intro r
    have hsum : (∑ j : Fin n, cutSign r j • x j) =
        R⁻¹ • ∑ j : Fin n, cutSign r j • C00.jColumn n m j.val := by
      calc
        _ = ∑ j : Fin n, R⁻¹ • (cutSign r j • C00.jColumn n m j.val) := by
          apply Finset.sum_congr rfl
          intro j _
          exact smul_comm _ _ _
        _ = _ := Finset.smul_sum.symm
    rw [hsum, N.smul, abs_of_pos (inv_pos.mpr hR), mul_comm R⁻¹, ← div_eq_mul_inv]
    apply (lt_div_iff₀ hR).mpr
    have hlower := N.jColumn_cut_lower hsub n m hn r
    change (n : ℝ) * R - 2 * (n : ℝ) * N (C00.basis 0) ≤ _ at hlower
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hscaled := mul_lt_mul_of_pos_left hbudget hnreal
    nlinarith

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
