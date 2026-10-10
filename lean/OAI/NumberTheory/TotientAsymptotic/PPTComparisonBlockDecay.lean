import OAI.NumberTheory.TotientAsymptotic.PPTComparisonScaleDecay

namespace OAI

/-!
The finite Ford comparison sum with its actual reciprocal masses.  The
geometric and normality conditions remain explicit; the logarithmic
dimension range and strict exponent saving absorb all the scalar costs.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The exact comparison-sum expression has an arbitrary inverse-power
saving once the local geometric bounds and finite mass bound hold. -/
theorem ppt_comparison_mass_decay {C A γ M : ℝ} (hC : 0 < C)
    (hA : 0 ≤ A) (hγ : 0 < γ) (d : ℕ) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop, ∀ (b h : ℕ) (W V Rmass Amass Q : ℝ) (Y U : ℕ → ℝ),
      1 ≤ b → (b : ℝ) ≤ A*Real.log (B z) → (h : ℝ) ≤ A*Real.log (B z) →
      1 < Y b → B (Y b) ≤ 2*(B z)^(2/3 : ℝ) →
      0 ≤ B V → B V ≤ 2*(B z)^(2/3 : ℝ) →
      Rmass*Amass ≤ Real.exp (M*(Real.log (B z))^2) →
      -2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B z))+
        comparisonError b z W Y U ≤ -1-γ/(Real.log (B z))^3 →
      Q ≤ z/(d : ℝ)*pptComparisonScale C b z W Y U*
        ((b+1 : ℝ)^d.primeFactorsList.length*
          Real.exp (4*(h : ℝ)*B V*Real.log (b+1)))*Rmass*Amass →
      Q ≤ z/((d : ℝ)*Real.log z)*(B z)^(-K) := by
  filter_upwards [ppt_full_comparison_decay hC hA hγ d.primeFactorsList.length K,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with z hdecay hB hz
  intro b h W V Rmass Amass Q Y U hb hbL hhL hY hBY hV0 hV hmass hE hcount
  let E : ℝ := -2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B z))+
    comparisonError b z W Y U
  let base : ℝ := (C*B z)^(6*b)*
    (Real.log (Y b))^(20*(b : ℝ)*Real.log b+1)*
    (b+1 : ℝ)^d.primeFactorsList.length*
    Real.exp (4*(h : ℝ)*B V*Real.log (b+1))
  have hlogY : 0 < Real.log (Y b) := Real.log_pos hY
  have hbase : 0 ≤ base := by
    dsimp only [base]
    positivity
  have hpow : 0 ≤ (Real.log z)^E :=
    Real.rpow_nonneg (Real.log_pos hz).le _
  have hmass' : base*(Rmass*Amass) ≤ base*Real.exp (M*(Real.log (B z))^2) :=
    mul_le_mul_of_nonneg_left hmass hbase
  have hscalar : pptComparisonScale C b z W Y U*
      ((b+1 : ℝ)^d.primeFactorsList.length*
        Real.exp (4*(h : ℝ)*B V*Real.log (b+1)))*Rmass*Amass ≤
      pptFullComparisonPrefactor C (B z) b d.primeFactorsList.length h
        (Real.log (Y b)) (B V) M*(Real.log z)^E := by
    calc
      _ = (base*(Rmass*Amass))*(Real.log z)^E := by
        dsimp only [pptComparisonScale, base, E]
        ring
      _ ≤ (base*Real.exp (M*(Real.log (B z))^2))*(Real.log z)^E :=
        mul_le_mul_of_nonneg_right hmass' hpow
      _ = _ := by
        dsimp only [pptFullComparisonPrefactor, base]
  have hsaved := hdecay b h (Real.log (Y b)) (B V) E hb hbL hhL
    (Real.log_pos hY) hBY hV0 hV hE
  calc
    Q ≤ z/(d : ℝ)*(pptComparisonScale C b z W Y U*
        ((b+1 : ℝ)^d.primeFactorsList.length*
          Real.exp (4*(h : ℝ)*B V*Real.log (b+1)))*Rmass*Amass) := by
      convert hcount using 1
      ring
    _ ≤ z/(d : ℝ)*((Real.log z)⁻¹*(B z)^(-K)) :=
      mul_le_mul_of_nonneg_left (hscalar.trans hsaved) (by positivity)
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The actual finite family of normal-tail comparison blocks satisfies
the saved bound.  In particular no estimate for those blocks is assumed
in this application theorem. -/
theorem ppt_normal_tail_block_decay (d : ℕ) (hd : 0 < d)
    {A γ M : ℝ} (hA : 0 ≤ A) (hγ : 0 < γ) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop, ∀ (b h : ℕ) (W V : ℝ) (Y U : ℕ → ℝ)
      (R Tails : Finset ℕ) (T : ℕ → ℕ → Finset ℕ)
      (tail : ℕ → Fin h → ℕ) (t : ℕ → ℕ → ℕ → ShiftedPair b),
      1 ≤ b → (b : ℝ) ≤ A*Real.log (B z) → (h : ℝ) ≤ A*Real.log (B z) →
      1 < W → 0 ≤ B W → W ≤ V → 1 < Y b →
      B (Y b) ≤ 2*(B z)^(2/3 : ℝ) → 0 ≤ B V → B V ≤ 2*(B z)^(2/3 : ℝ) →
      (∑ c ∈ R, 1/(c.totient : ℝ))*(∑ a ∈ Tails, 1/(a.totient : ℝ)) ≤
        Real.exp (M*(Real.log (B z))^2) →
      -2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B z))+
        comparisonError b z W Y U ≤ -1-γ/(Real.log (B z))^3 →
      (∀ a ∈ Tails, a = ∏ i, tail a i) →
      (∀ a ∈ Tails, Function.Injective (tail a)) →
      (∀ a ∈ Tails, ∀ i, IsNormalPrime W (tail a i)) →
      (∀ a ∈ Tails, ∀ i, (largestPrimeFactor (tail a i-1) : ℝ) ≤ V) →
      (∀ c ∈ R, ∀ a ∈ Tails,
        FordComparisonParameters b z W (d*a.totient) c.totient Y U) →
      (∀ c ∈ R, ∀ a ∈ Tails, ∀ n ∈ T c a, n = c*a*∏ i, (t c a n).left i) →
      (∀ c ∈ R, ∀ a ∈ Tails, ∀ n ∈ T c a,
        FordComparisonConditions b z W (d*a.totient) c.totient Y U (t c a n)) →
      (∑ c ∈ R, ∑ a ∈ Tails, ((T c a).card : ℝ)) ≤
        z/((d : ℝ)*Real.log z)*(B z)^(-K) := by
  obtain ⟨C, z₀, hC, _, hsum⟩ := ppt_plain_normal_tail_comparison_sum
  filter_upwards [ppt_comparison_mass_decay hC hA hγ d K,
    eventually_ge_atTop z₀,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with z hdecay hz hB
  intro b h W V Y U R Tails T tail t hb hbL hhL hW hBW hWV hY hBY hV0 hV
    hmass hE htail hinj hnormal hsmall hparams hreal hconditions
  apply hdecay b h W V
    (∑ c ∈ R, 1/(c.totient : ℝ)) (∑ a ∈ Tails, 1/(a.totient : ℝ))
    (∑ c ∈ R, ∑ a ∈ Tails, ((T c a).card : ℝ)) Y U
    hb hbL hhL hY hBY hV0 hV hmass hE
  exact hsum b d h z W V Y U R Tails T tail t hd hz hB.le hW hBW hWV hY.le
    htail hinj hnormal hsmall hparams hreal hconditions

end TotientAsymptotic

end

end OAI
