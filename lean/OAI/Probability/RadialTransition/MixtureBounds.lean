import OAI.Probability.RadialTransition.CountWeights

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

def quadraticTerm (φ : Potential) (L β z b : ℝ) (n : ℕ) : ℝ :=
  Real.exp (z*n) * partition φ L n β * Real.exp (b*(n:ℝ)^2/L^3)

lemma quadraticTerm_pos {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L : ℝ} (hL : 0 < L) (β z b : ℝ) (n : ℕ) : 0 < quadraticTerm φ L β z b n := by
  exact mul_pos (mul_pos (Real.exp_pos _) (partition_pos hφ hb hL n β)) (Real.exp_pos _)

lemma quadraticTerm_tail_bound {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L β z b c B κ D : ℝ} (hL : 0 < L) (hβ : 0 ≤ β) (hκ : 0 < κ)
    (hc : κ ≤ β*c-b) (hD : 1 ≤ D) (hcut : z+β*B+2 ≤ κ*D)
    (hE : ∀ n x, x ∈ configurationCube L n → c*(n:ℝ)^2/L^3-B*n ≤ energy φ x)
    {n : ℕ} (hn : D*L^3 < n) : quadraticTerm φ L β z b n ≤ Real.exp (-(n:ℝ)) := by
  have hV : 0 < L^3 := by positivity
  have hn0 : 0 < (n:ℝ) := lt_trans (by positivity : 0 < D*L^3) hn
  have hp := quadraticTerm_pos hφ hb hL β z b n
  have hl := log_partition_upper_of_energy_lower hφ hb hL hβ n (hE n)
  have hf := (log_factorial_bounds n).1
  have hlog : Real.log (L^3) ≤ Real.log (n:ℝ) := Real.log_le_log hV (by nlinarith)
  have hentropy : (n:ℝ)*Real.log (L^3)-Real.log (n.factorial:ℝ) ≤ n := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hn0.le]
  have hquad : κ*D*(n:ℝ) ≤ (β*c-b)*(n:ℝ)^2/L^3 := by
    apply (le_div_iff₀ hV).mpr
    have hh : D*L^3 ≤ (n:ℝ) := hn.le
    nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg hκ.le hn0.le),
      mul_le_mul_of_nonneg_right hc (sq_nonneg (n:ℝ))]
  have hlg : Real.log (quadraticTerm φ L β z b n) ≤ -(n:ℝ) := by
    rw [quadraticTerm, Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (partition_pos hφ hb hL n β).ne') (Real.exp_ne_zero _),
      Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL n β).ne', Real.log_exp, Real.log_exp]
    have he : z*(n:ℝ)-β*(c*(n:ℝ)^2/L^3-B*n)+b*(n:ℝ)^2/L^3 =
        (z+β*B)*(n:ℝ)-(β*c-b)*(n:ℝ)^2/L^3 := by ring
    have hh := mul_le_mul_of_nonneg_right hcut hn0.le
    linarith
  exact (Real.exp_log hp).symm.le.trans (Real.exp_le_exp.mpr hlg)

lemma exp_neg_nat_summable : Summable (fun n : ℕ => Real.exp (-(n:ℝ))) := by
  have he (n : ℕ) : Real.exp (-(n:ℝ)) = (Real.exp (-1))^n := by rw [← Real.exp_nat_mul]; congr 1; ring
  simpa only [he] using summable_geometric_of_lt_one (Real.exp_pos (-1)).le (Real.exp_lt_one_iff.mpr (by norm_num))

lemma exp_neg_positive_tail : (∑' n : {n : ℕ // 0 < n}, Real.exp (-(n:ℝ))) ≤ 1 := by
  have hs := exp_neg_nat_summable
  have he : (∑' n : ℕ, Real.exp (-(n:ℝ))) = (1-Real.exp (-1))⁻¹ := by
    have hh := tsum_geometric_of_lt_one (Real.exp_pos (-1)).le (Real.exp_lt_one_iff.mpr (by norm_num))
    convert hh using 1
    apply tsum_congr; intro n
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hx : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]
    have hh := Real.add_one_le_exp (1:ℝ)
    linarith
  have hpos : 0 < 1-Real.exp (-1) := by linarith
  have hsum : (∑' n : ℕ, Real.exp (-(n:ℝ))) ≤ 2 := by
    rw [he, inv_le_iff_one_le_mul₀ hpos]
    linarith
  have ht := hs.sum_add_tsum_compl (s := {0})
  simp only [Finset.sum_singleton, Nat.cast_zero, neg_zero, Real.exp_zero] at ht
  have heq : (∑' n : {n : ℕ // n ∉ ({0}:Finset ℕ)}, Real.exp (-(n:ℝ))) =
      ∑' n : {n : ℕ // 0 < n}, Real.exp (-(n:ℝ)) := by
    let e : {n : ℕ // n ∉ ({0}:Finset ℕ)} ≃ {n : ℕ // 0 < n} :=
      Equiv.subtypeEquivProp (by funext n; apply propext; simp [Nat.pos_iff_ne_zero])
    exact e.tsum_eq (fun n => Real.exp (-(n:ℝ)))
  change 1 + (∑' n : {n : ℕ // n ∉ ({0}:Finset ℕ)}, Real.exp (-(n:ℝ))) = _ at ht
  rw [heq] at ht
  linarith

lemma summable_of_tail_exp {F : ℕ → ℝ} (hF : ∀ n, 0 ≤ F n) (N : ℕ)
    (htail : ∀ n, N < n → F n ≤ Real.exp (-(n:ℝ))) : Summable F := by
  apply Summable.of_nonneg_of_le (fun n => hF n) (f := fun n => if n ≤ N then F n else Real.exp (-(n:ℝ)))
  · intro n
    split_ifs with hn
    · rfl
    · exact htail n (by omega)
  · have he : (fun n => if n ≤ N then F n else Real.exp (-(n:ℝ))) =
        (fun n : ℕ => Real.exp (-(n:ℝ)) + if n ≤ N then F n-Real.exp (-(n:ℝ)) else 0) := by
      funext n; split_ifs <;> ring
    rw [he]
    exact exp_neg_nat_summable.add (summable_of_ne_finset_zero (s := Finset.range (N+1)) (by intro n hn; simp only [Finset.mem_range, not_lt] at hn; simp [show ¬n ≤ N by omega]))

lemma tail_le_one_of_exp {F : ℕ → ℝ} (hF : ∀ n, 0 ≤ F n) (N : ℕ)
    (htail : ∀ n, N < n → F n ≤ Real.exp (-(n:ℝ))) :
    (∑' n : {n : ℕ // N < n}, F n) ≤ 1 := by
  have hs := summable_of_tail_exp hF N htail
  have hh := (hs.subtype (fun n => N < n)).tsum_le_tsum (fun (n : {n : ℕ // N < n}) => htail n n.property)
    (exp_neg_nat_summable.subtype (fun n => N < n))
  apply hh.trans
  apply le_trans _ exp_neg_positive_tail
  let j : {n : ℕ // N < n} → {n : ℕ // 0 < n} := fun n => ⟨n, lt_of_le_of_lt (Nat.zero_le N) n.property⟩
  exact tsum_comp_le_tsum_of_inj (i := j) (exp_neg_nat_summable.subtype (fun n => 0 < n))
    (fun _ => (Real.exp_pos _).le) (by intro a b h; apply Subtype.ext; exact congrArg (fun x : {n : ℕ // 0 < n} => (x:ℕ)) h)

lemma truncated_sum_bound {F : ℕ → ℝ} (hF : Summable F) {N : ℕ} {M : ℝ}
    (hM : 1 ≤ M) (htail : (∑' n : {n : ℕ // N < n}, F n) ≤ 1)
    (hsmall : ∀ n, n ≤ N → F n ≤ M) : (∑' n, F n) ≤ ((N:ℝ)+2)*M := by
  have ht := hF.sum_add_tsum_compl (s := Finset.range (N+1))
  have he := (Equiv.subtypeEquivProp (by funext n; apply propext; simp) :
    {n : ℕ // n ∉ Finset.range (N+1)} ≃ {n : ℕ // N < n}).tsum_eq (fun n => F n)
  change (∑' n : {n : ℕ // n ∉ Finset.range (N+1)}, F n) =
    (∑' n : {n : ℕ // N < n}, F n) at he
  change (∑ n ∈ Finset.range (N+1), F n) + (∑' n : {n : ℕ // n ∉ Finset.range (N+1)}, F n) = _ at ht
  rw [he] at ht
  have hs := Finset.sum_le_card_nsmul (Finset.range (N+1)) F M (by intro n hn; exact hsmall n (by simpa using hn))
  simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hs
  linarith

end RadialTransition

end

end OAI
