import OAI.NumberTheory.TotientAsymptotic.TailVolume
import OAI.NumberTheory.TotientAsymptotic.RenewalLower

namespace OAI

/-! A terminal tail prime forces lower bounds throughout the actual witness region. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prefixLinear_terminal_lower {N : ℕ} (u : Fin N → ℝ) (T : ℝ)
    (hu : ∀ i, a (N-i.val)*T ≤ prefixLinear N u i) :
    ∀ i, g (N-i.val)*T ≤ u i := by
  let v : ℕ → ℝ := fun j => if hj : j < N then u ⟨j, hj⟩ else T
  have hv (j : ℕ) (hj : j < N) : v j = u ⟨j, hj⟩ := by simp [v, hj]
  have hvN : v N = T := by simp [v]
  have hslack (i : ℕ) (hi : i < N) :
      (∑ j ∈ Finset.Icc (i+1) N, a (j-i)*v j) ≤ v i := by
    let i' : Fin N := ⟨i, hi⟩
    have hh := hu i'
    rw [prefixLinear_apply] at hh
    have hsum : (∑ j : Fin N, if i' < j then a (j.val-i'.val)*u j else 0) =
        ∑ j ∈ Finset.Icc (i+1) (N-1), a (j-i)*v j := by
      have heq : (∑ j : Fin N, if i' < j then a (j.val-i'.val)*u j else 0) =
          ∑ j : Fin N, if i < j.val then a (j.val-i)*v j.val else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        change (if i < j.val then a (j.val-i)*u j else 0) = _
        rw [hv j.val j.isLt]
      rw [heq, Fin.sum_univ_eq_sum_range
        (fun k => if i < k then a (k-i)*v k else 0), ← Finset.sum_filter]
      have he : (Finset.range N).filter (fun j => i < j) = Finset.Icc (i+1) (N-1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        omega
      rw [he]
    rw [hsum] at hh
    have hsplit : (∑ j ∈ Finset.Icc (i+1) N, a (j-i)*v j) =
        (∑ j ∈ Finset.Icc (i+1) (N-1), a (j-i)*v j)+a (N-i)*T := by
      have hN : N-1+1=N := by omega
      rw [← hN, Finset.sum_Icc_succ_top (by omega : i+1 ≤ N-1+1), hN, hvN]
    rw [hsplit, hv i hi]
    change a (N-i)*T ≤ u ⟨i, hi⟩ - _ at hh
    linarith
  intro i
  simpa only [hvN, hv i.val i.isLt] using
    (renewal_prefix_lower N v hslack (Nat.le_of_lt i.isLt))

lemma tail_threshold_terminal {H h : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) (hPH : P H < H) (hh : H ≤ h) :
    a (h-(H-1))*tailLog η (H-1) ≤ D h η := by
  have hlast : H-1 ∈ Finset.Ico (P H) H := Finset.mem_Ico.mpr (by omega)
  unfold D
  apply Finset.single_le_sum (f := fun l : ℕ => a (h-l)*tailLog η l)
  · intro j hj
    have hj' := Finset.mem_Ico.mp hj
    exact mul_nonneg (a_pos (by omega)).le (tailLog_nonneg hη hj)
  · exact hlast

/-- Every coordinate of an unbanded witness region retains the contribution
of the first discrete tail prime. This is the manuscript's recurrence bound. -/
theorem tailPrefixRegion_terminal_lower {x s : ℝ} {H : ℕ} {η : TailDatum H}
    (hη : IsWitness H s η) (hPH : P H < H) (hHm : H ≤ m x)
    {u : Fin (R x H) → ℝ} (hu : u ∈ tailPrefixRegion x H η) :
    ∀ i, g (R x H-i.val)*tailLog η (H-1) ≤ u i := by
  apply prefixLinear_terminal_lower
  intro i
  have hh : H ≤ m x-(i.val+1) := by have := i.isLt; unfold R at *; omega
  have he : m x-(i.val+1)-(H-1) = R x H-i.val := by
    have := i.isLt
    unfold R at *
    omega
  have hb := tail_threshold_terminal hη hPH hh
  rw [he] at hb
  exact hb.trans (hu.1 i)

end TotientAsymptotic

end

end OAI
