import OAI.NumberTheory.TotientAsymptotic.CollisionDyadicCount
import Mathlib.Data.Nat.Log

namespace OAI

/-! A finite dyadic quotient can be integrated from its actual lowest slice. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma dyadic_nat_bounds {v : ℕ} (hv : 1 < v) :
    1 ≤ Nat.clog 2 v ∧ (2 : ℝ)^(Nat.clog 2 v)/2 < v ∧
      (v : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 v) := by
  have hn : 1 ≤ Nat.clog 2 v := by
    have hh := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2) (x := v) (y := 0)).mpr
      (by simpa using hv)
    omega
  refine ⟨hn,?_,?_⟩
  · have hh := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hv
    have he : Nat.clog 2 v=Nat.clog 2 v-1+1 := by omega
    rw [he,pow_succ]
    have hcast : (2 : ℝ)^(Nat.clog 2 v-1) < v := by exact_mod_cast hh
    convert hcast using 1
    ring
  · exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) v

lemma dyadic_endpoint_log (n : ℕ) :
    Real.log ((2 : ℝ)^n)=(n : ℝ)*Real.log 2 := by rw [Real.log_pow]

lemma dyadic_endpoint_B (n : ℕ) :
    B ((2 : ℝ)^n)=Real.log ((n : ℝ)*Real.log 2) := by
  rw [B,dyadic_endpoint_log]

/-- The dyadic count can be integrated using only a lower bound at the
occupied slices. Empty slices require no separate counting hypothesis. -/
theorem finite_dyadic_collision_mass {α : Type*} (Q : Finset α)
    (n : α → ℕ) (v : α → ℝ) {C σ B : ℝ}
    (hC : 0 ≤ C) (hσ : 0 < σ)
    (hstart : ∀ a ∈ Q, 2 ≤ n a ∧ Real.exp B ≤ ((n a-1 : ℕ) : ℝ)*Real.log 2)
    (hlo : ∀ a ∈ Q, (2 : ℝ)^(n a)/2 < v a)
    (hcount : ∀ k : ℕ, ((Q.filter (fun a => n a=k)).card : ℝ) ≤
      C*(2 : ℝ)^k*dyadicSuffixWeight σ k) :
    (∑ a ∈ Q, (v a)⁻¹) ≤ (2*C)/(σ*Real.log 2)*Real.exp (-σ*B) := by
  classical
  by_cases hQ : Q.Nonempty
  · let T := Q.image n
    have hT : T.Nonempty := hQ.image n
    let n₀ := T.min' hT
    have hn₀ : n₀ ∈ T := Finset.min'_mem T hT
    obtain ⟨a₀,ha₀,he₀⟩ := Finset.mem_image.mp hn₀
    have hs := hstart a₀ ha₀
    rw [he₀] at hs
    let N := n₀-1
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hmin (a : α) (ha : a ∈ Q) : n₀ ≤ n a :=
      Finset.min'_le T (n a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
    let idx := fun a => n a-N-1
    have he (a : α) (ha : a ∈ Q) : idx a+N+1=n a := by
      have hh := hmin a ha
      dsimp [idx,N]
      omega
    apply collision_dyadic_reciprocal_bound Q idx v hN hC hσ hs.2
    · intro a ha
      simpa only [he a ha] using hlo a ha
    · intro k
      have hf : Q.filter (fun a => idx a=k)=Q.filter (fun a => n a=k+N+1) := by
        ext a
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨ha,hk⟩
          exact ⟨ha,by rw [← he a ha,hk]⟩
        · rintro ⟨ha,hk⟩
          refine ⟨ha,?_⟩
          have hh := he a ha
          omega
      rw [hf]
      exact hcount _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hQ]
    simp only [Finset.sum_empty]
    positivity

lemma dyadic_band_start {b : ℝ} {n : ℕ} (hb : 100 ≤ b) (hn : 1 ≤ n)
    (hband : (87/100 : ℝ)*b ≤ B ((2 : ℝ)^n)) :
    2 ≤ n ∧ Real.exp (b/2) ≤ ((n-1 : ℕ) : ℝ)*Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnl : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow := Real.exp_le_exp.mpr hband
  rw [dyadic_endpoint_B,Real.exp_log (mul_pos hnl hlog2)] at hpow
  have hlarge : Real.log 2 ≤ Real.exp (b/2) := by
    have he := Real.add_one_le_exp (b/2)
    linarith [Real.log_two_lt_d9]
  have hfactor : 2 ≤ Real.exp ((37/100 : ℝ)*b) := by
    have he := Real.add_one_le_exp ((37/100 : ℝ)*b)
    linarith
  have heq : Real.exp ((87/100 : ℝ)*b)=
      Real.exp (b/2)*Real.exp ((37/100 : ℝ)*b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdouble : 2*Real.exp (b/2) ≤ (n : ℝ)*Real.log 2 := by
    rw [heq] at hpow
    nlinarith [Real.exp_pos (b/2)]
  have hsub : ((n-1 : ℕ) : ℝ)=(n : ℝ)-1 := by
    rw [Nat.cast_sub hn,Nat.cast_one]
  have hbnd : Real.exp (b/2) ≤ ((n-1 : ℕ) : ℝ)*Real.log 2 := by
    rw [hsub]
    nlinarith
  refine ⟨?_,hbnd⟩
  by_contra hn2
  have hn1 : n=1 := by omega
  rw [hn1] at hbnd
  norm_num at hbnd
  exact (Real.exp_pos _).not_ge hbnd

end TotientAsymptotic

end

end OAI
