import OAI.NumberTheory.TotientAsymptotic.SmoothCofactorTail
import OAI.NumberTheory.TotientAsymptotic.Mass

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma smooth_cutoff_bounds {x : ℝ} {i : ℕ} (hb : 2 ≤ bandScale x i) :
    2 ≤ remainderPrimeBound x i ∧
      Real.log (remainderPrimeBound x i : ℝ) ≤ 2*Real.exp ((11/10 : ℝ)*bandScale x i) := by
  let b := bandScale x i
  let Y := Real.exp (Real.exp ((11/10 : ℝ)*b))
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hY : 2 ≤ Y := by
    have hinner := Real.add_one_le_exp ((11/10 : ℝ)*b)
    have houter := Real.add_one_le_exp (Real.exp ((11/10 : ℝ)*b))
    dsimp [Y]
    linarith
  have hceil := Nat.le_ceil Y
  have hceil2 : 2 ≤ ⌈Y⌉₊ := by exact_mod_cast hY.trans hceil
  have he : remainderPrimeBound x i=⌈Y⌉₊ := by
    change max 1 ⌈Y⌉₊=⌈Y⌉₊
    exact max_eq_right (by omega)
  rw [he]
  refine ⟨hceil2,?_⟩
  have hupper : (⌈Y⌉₊ : ℝ) ≤ 2*Y := by
    have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ Y)
    linarith
  calc
    _ ≤ Real.log (2*Y) := Real.log_le_log (by exact_mod_cast (show 0<⌈Y⌉₊ by omega)) hupper
    _ = Real.log 2+Real.exp ((11/10 : ℝ)*b) := by
      rw [Real.log_mul (by norm_num) (by positivity : Y ≠ 0)]
      simp only [Y,Real.log_exp]
    _ ≤ _ := by
      have hl := Real.log_two_lt_d9
      have he := Real.one_le_exp (show 0 ≤ (11/10 : ℝ)*b by positivity)
      linarith

lemma rankin_decay : ∀ᶠ b : ℝ in atTop,
    (22/5 : ℝ)*b-Real.exp ((9/10 : ℝ)*b)/8 ≤ -b := by
  have ht : Tendsto (fun b : ℝ => b*Real.exp (-(9/10 : ℝ)*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (9/10) (by norm_num : (0 : ℝ)<9/10)
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<5/216))] with b hb
  have hh := mul_le_mul_of_nonneg_right hb.le (Real.exp_pos ((9/10 : ℝ)*b)).le
  rw [mul_assoc,← Real.exp_add] at hh
  simp only [neg_mul,neg_add_cancel,Real.exp_zero,mul_one] at hh
  linarith

theorem smooth_cutoff_tail (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ b : ℝ in atTop, ∀ x : ℝ, ∀ i : ℕ,
      bandScale x i=b → ∀ Q : Finset ℕ,
      (∀ n ∈ Q, 0<n ∧ largestPrimeFactor n ≤ remainderPrimeBound x i ∧
        Real.exp (2*b)<Real.log n) →
      (∑ n ∈ Q, (n.totient : ℝ)⁻¹) ≤ C*Real.exp (-b) := by
  obtain ⟨D,hD,hbound⟩ := hmertens
  refine ⟨16*D^4,by positivity,?_⟩
  filter_upwards [rankin_decay,eventually_ge_atTop (2 : ℝ)] with b hdec hb
  intro x i hi Q hQ
  have hcut := smooth_cutoff_bounds (hi.symm ▸ hb)
  let N := remainderPrimeBound x i
  have hN : 2 ≤ N := hcut.1
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hlog : Real.log (N : ℝ) ≤ 2*Real.exp ((11/10 : ℝ)*b) := by simpa only [hi] using hcut.2
  have hm := smooth_cofactor_rankin hN (Real.exp (2*b)) Q hQ
  have hsave : Real.exp ((9/10 : ℝ)*b)/8 ≤ Real.exp (2*b)/(4*Real.log N) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ = (Real.exp ((9/10 : ℝ)*b)/2)*Real.log N := by ring
      _ ≤ (Real.exp ((9/10 : ℝ)*b)/2)*(2*Real.exp ((11/10 : ℝ)*b)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = Real.exp ((9/10 : ℝ)*b)*Real.exp ((11/10 : ℝ)*b) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hprod := hbound N hN
  have hE0 : 0 ≤ primeEulerProduct N := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ)<p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  calc
    _ ≤ Real.exp (-Real.exp (2*b)/(4*Real.log N))*(D*Real.log N)^4 :=
      hm.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE0 hprod 4) (Real.exp_pos _).le)
    _ ≤ Real.exp (-Real.exp ((9/10 : ℝ)*b)/8)*(D*(2*Real.exp ((11/10 : ℝ)*b)))^4 := by
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        simpa only [neg_div] using neg_le_neg hsave
      · exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hlog hD.le) 4
      · positivity
      · exact (Real.exp_pos _).le
    _ = (16*D^4)*Real.exp ((22/5 : ℝ)*b-Real.exp ((9/10 : ℝ)*b)/8) := by
      have he : (Real.exp ((11/10 : ℝ)*b))^4=Real.exp ((22/5 : ℝ)*b) := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
        ring
      rw [mul_pow,mul_pow,he]
      rw [show (22/5 : ℝ)*b-Real.exp ((9/10 : ℝ)*b)/8 =
        (-Real.exp ((9/10 : ℝ)*b)/8)+(22/5 : ℝ)*b by ring,Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdec) (by positivity)

end TotientAsymptotic

end

end OAI
