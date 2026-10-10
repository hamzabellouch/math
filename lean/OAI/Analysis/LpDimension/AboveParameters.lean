import OAI.Analysis.LpDimension.CutoffEnvelope

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u

namespace SubpolynomialLp

lemma above_small_error (R : ℝ) (hR : 3 < R) :
    let ε := 1/(28*R)
    0 < ε ∧ ((1+ε)^3-1) ≤ 1/(2*R) := by
  let ε := 1/(28*R)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεR : ε*(28*R)=1 := div_mul_cancel₀ 1 (by positivity)
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hε2 : ε^2 ≤ ε := by nlinarith [mul_le_mul_of_nonneg_left hε1 hε.le]
  have hε3 : ε^3 ≤ ε := by
    have hh := mul_le_mul_of_nonneg_left hε2 hε.le
    nlinarith
  refine ⟨hε,?_⟩
  calc
    _ ≤ 7*ε := by nlinarith
    _ ≤ 1/(2*R) := (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hεR])

lemma above_numeric_parameters (p R C β : ℝ) (hp : 2 < p) (hR : 3 < R)
    (hC : 0 < C) (hβ : β ≤ 1/(2*R)) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 2 ≤ n → ∃ (ℓ : ℕ) (T : ℝ),
      let H := 4*Real.log (n:ℝ)
      let J := (aboveVariance p+1)*H*2^(2*ℓ)
      let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
      0 ≤ T ∧ T ≤ H^2*Real.exp (A*(H^(1-2/p)+1)) ∧ 1 ≤ b/R ∧
      β*b+C*H^(p-2)*((ℓ:ℝ)+1)+C*J^p*Real.exp (-T/(2*J))*(n:ℝ)^2 ≤ b/R := by
  have hp0 : 0 < p := by linarith
  have hR0 : 0 < R := by linarith
  let c := p*Real.log 2
  have hc : 0 < c := by dsimp [c]; positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  let L := 2*R*(3*C+1)/c+1
  have hL : 1 ≤ L := by
    dsimp [L]
    exact le_add_of_nonneg_left (by positivity)
  have hcL : 2*R*(3*C+1) ≤ c*L := by
    have he : c*L=2*R*(3*C+1)+c := by dsimp [L]; field_simp
    rw [he]
    linarith
  have hr0 : 0 < 1-2/p := by apply sub_pos.mpr; exact (div_lt_one hp0).mpr hp
  have hr1 : 1-2/p < 1 := by
    have hh : 0 < 2/p := by positivity
    linarith
  have hU := aboveVariance_pos p hp
  obtain ⟨A,hA,hEnvelope⟩ := ramp_cutoff_envelope p C (aboveVariance p) L (1-2/p) hp0 hC hU hL hr0 hr1
  refine ⟨A,hA,fun n hn => ?_⟩
  let H := 4*Real.log (n:ℝ)
  have hH : 1 ≤ H := by have hh := log_nat_lower n hn; dsimp [H]; linarith
  have hH0 : 0 < H := by linarith
  let m := ⌈L*(H^(1-2/p)+1)⌉₊+1
  let ℓ := 2*m
  let J := (aboveVariance p+1)*H*2^(2*ℓ)
  let T := 2*J*(p*Real.log J+H+Real.log (C+1))
  let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
  have hm1 : 1 ≤ m := by dsimp [m]; omega
  have hm1R : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hm0 : (0:ℝ) < m := by linarith
  have hmp : L*H^(p-2) ≤ (m:ℝ)^p := by
    have hmL : L*H^(1-2/p) ≤ (m:ℝ) := by
      have hh := Nat.le_ceil (L*(H^(1-2/p)+1))
      dsimp [m]
      push_cast
      nlinarith
    have hLp : L ≤ L^p := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL (by linarith : (1:ℝ) ≤ p)
    have hexp : (H^(1-2/p))^p=H^(p-2) := by
      rw [← Real.rpow_mul hH0.le]
      congr 1
      field_simp
    calc
      _ ≤ L^p*H^(p-2) := mul_le_mul_of_nonneg_right hLp (Real.rpow_nonneg hH0.le _)
      _ = (L*H^(1-2/p))^p := by rw [Real.mul_rpow (by linarith : 0 ≤ L) (Real.rpow_nonneg hH0.le _),hexp]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hmL hp0.le
  have hHp : 1 ≤ H^(p-2) := Real.one_le_rpow hH (by linarith)
  have hb0 : 0 ≤ b := integral_nonneg (fun r => Real.rpow_nonneg (abs_nonneg _) _)
  have henergy : c*(m:ℝ)^p*(m:ℝ) ≤ b := by
    have hh := pareto_dyadicRamp_energy_lower p hp0 m hm1
    rw [Real.rpow_add_one hm0.ne'] at hh
    change c*((m:ℝ)^p*(m:ℝ)) ≤ b at hh
    nlinarith only [hh]
  have hbBig : 2*R*(3*C+1)*(m:ℝ)*H^(p-2) ≤ b := by
    have h₁ := mul_le_mul_of_nonneg_right hcL (show 0 ≤ (m:ℝ)*H^(p-2) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hmp (show 0 ≤ c*(m:ℝ) by positivity)
    nlinarith only [h₁,h₂,henergy]
  have hrest : C*H^(p-2)*((ℓ:ℝ)+1)+1 ≤ b/(2*R) := by
    have hmh : 1 ≤ (m:ℝ)*H^(p-2) := by nlinarith
    have hm3 : (ℓ:ℝ)+1 ≤ 3*(m:ℝ) := by dsimp [ℓ]; push_cast; linarith
    have hcore := mul_le_mul_of_nonneg_left hm3 (show 0 ≤ C*H^(p-2) by positivity)
    have hh : C*H^(p-2)*((ℓ:ℝ)+1)+1 ≤ (3*C+1)*(m:ℝ)*H^(p-2) := by nlinarith only [hcore,hmh]
    apply (le_div_iff₀ (by positivity : 0 < 2*R)).mpr
    have hr := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*R by positivity)
    nlinarith only [hr,hbBig]
  have hbR : R ≤ b := by
    have hc0 : 0 ≤ C*H^(p-2)*((ℓ:ℝ)+1) := by positivity
    have hh := (le_div_iff₀ (by positivity : 0 < 2*R)).mp hrest
    nlinarith
  have hEnv := hEnvelope H hH
  change 1 ≤ J ∧ 0 ≤ T ∧ T ≤ H^2*Real.exp (A*(H^(1-2/p)+1)) at hEnv
  have hJ : 0 < J := by linarith [hEnv.1]
  have htail := global_cutoff_tail p C J hC hJ n hn
  change C*J^p*Real.exp (-T/(2*J))*(n:ℝ)^2 ≤ 1 at htail
  refine ⟨ℓ,T,hEnv.2.1,hEnv.2.2,(le_div_iff₀ hR0).mpr (by simpa only [one_mul] using hbR),?_⟩
  have hbet := mul_le_mul_of_nonneg_right hβ hb0
  have hhalf : (1/(2*R))*b+b/(2*R)=b/R := by ring
  calc
    _ ≤ (1/(2*R))*b+(C*H^(p-2)*((ℓ:ℝ)+1)+1) := by linarith
    _ ≤ (1/(2*R))*b+b/(2*R) := by linarith only [hrest]
    _ = _ := hhalf

end SubpolynomialLp

end

end OAI
