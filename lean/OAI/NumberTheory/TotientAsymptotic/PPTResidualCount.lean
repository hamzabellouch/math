import OAI.NumberTheory.TotientAsymptotic.PPTHeadResidualFamily

namespace OAI

/-!
All residual block labels are summed before the strict comparison
exponent is spent. This retains the exponential-square budget needed
for variable dimensions, grid labels, common factors, and small tails.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The literal Ford bound, normal small-tail estimate, and strict
exponent together control any finite family of actual residual blocks.
The only aggregate quantity is the explicit reciprocal-factor mass. -/
theorem ppt_finite_residual_block_decay (d : ℕ) (hd : 0 < d)
    {A γ M : ℝ} (hA : 0 ≤ A) (hγ : 0 < γ) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (α : Type) (I : Finset α) (b h c a : α → ℕ) (W V : α → ℝ)
      (Y U : α → ℕ → ℝ) (tail : (i : α) → Fin (h i) → ℕ)
      (T : α → Finset ℕ) (t : (i : α) → ℕ → ShiftedPair (b i)),
      (∀ i ∈ I, 1 ≤ b i) →
      (∀ i ∈ I, (b i : ℝ) ≤ A*Real.log (B z)) →
      (∀ i ∈ I, (h i : ℝ) ≤ A*Real.log (B z)) →
      (∀ i ∈ I, 1 < W i ∧ 0 ≤ B (W i) ∧ W i ≤ V i) →
      (∀ i ∈ I, 1 < Y i (b i) ∧ B (Y i (b i)) ≤ 2*(B z)^(2/3 : ℝ)) →
      (∀ i ∈ I, 0 ≤ B (V i) ∧ B (V i) ≤ 2*(B z)^(2/3 : ℝ)) →
      (∑ i ∈ I, (1/((a i).totient : ℝ))*(1/((c i).totient : ℝ))) ≤
        Real.exp (M*(Real.log (B z))^2) →
      (∀ i ∈ I, a i = ∏ j, tail i j) →
      (∀ i ∈ I, Function.Injective (tail i)) →
      (∀ i ∈ I, ∀ j, IsNormalPrime (W i) (tail i j)) →
      (∀ i ∈ I, ∀ j, (largestPrimeFactor (tail i j-1) : ℝ) ≤ V i) →
      (∀ i ∈ I,
        -2+(∑ j ∈ Finset.Icc 1 (b i-1), TotientAsymptotic.a j*(B (Y i j)/B z))+
          comparisonError (b i) z (W i) (Y i) (U i) ≤
          -1-γ/(Real.log (B z))^3) →
      (∀ i ∈ I, FordComparisonParameters (b i) z (W i)
        (d*(a i).totient) (c i).totient (Y i) (U i)) →
      (∀ i ∈ I, ∀ n ∈ T i, n = c i*a i*∏ j, (t i n).left j) →
      (∀ i ∈ I, ∀ n ∈ T i, FordComparisonConditions (b i) z (W i)
        (d*(a i).totient) (c i).totient (Y i) (U i) (t i n)) →
      (∑ i ∈ I, ((T i).card : ℝ)) ≤ z/((d : ℝ)*Real.log z)*(B z)^(-K) := by
  classical
  obtain ⟨C, z₀, hC, _, hcount⟩ := ppt_plain_comparison_block_count
  filter_upwards [ppt_full_comparison_decay (M := M) hC hA hγ d.primeFactorsList.length K,
    eventually_ge_atTop z₀, eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with z hdecay hz₀ hz hB
  intro α I b h c a W V Y U tail T t hb hbL hhL hW hY hV hmass
    htail hinj hnormal hsmall hE hparams hreal hconditions
  let Q : ℝ := Real.exp (M*(Real.log (B z))^2)
  let L : ℝ := (Real.log z)⁻¹*(B z)^(-K)
  have hQ : 0 < Q := Real.exp_pos _
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hscalar : 0 ≤ z/(d : ℝ)*L := mul_nonneg (by positivity) hL
  have hblock (i : α) (hi : i ∈ I) :
      ((T i).card : ℝ)*Q ≤
        (z/(d : ℝ)*L)*((1/((a i).totient : ℝ))*(1/((c i).totient : ℝ))) := by
    let E : ℝ := -2+
      (∑ j ∈ Finset.Icc 1 (b i-1), TotientAsymptotic.a j*(B (Y i j)/B z))+
      comparisonError (b i) z (W i) (Y i) (U i)
    let F : ℝ := (C*B z)^(6*b i)*(Real.log (Y i (b i)))^(20*(b i : ℝ)*Real.log (b i)+1)*
      (b i+1 : ℝ)^d.primeFactorsList.length *
      Real.exp (4*(h i : ℝ)*B (V i)*Real.log (b i+1))*(Real.log z)^E
    have hcost : (b i+1 : ℝ)^((d*(a i).totient).primeFactorsList.length) ≤
        (b i+1 : ℝ)^d.primeFactorsList.length *
          Real.exp (4*(h i : ℝ)*B (V i)*Real.log (b i+1)) := by
      rw [htail i hi]
      exact ppt_small_tail_comparison_cost (b i) (tail i) hd (hnormal i hi)
        (hinj i hi) (hW i hi).1 (hW i hi).2.1 (hW i hi).2.2 (hsmall i hi)
    have hsaved : F*Q ≤ L := by
      have hh := hdecay (b i) (h i) (Real.log (Y i (b i))) (B (V i)) E
        (hb i hi) (hbL i hi) (hhL i hi) (Real.log_pos (hY i hi).1)
        (hY i hi).2 (hV i hi).1 (hV i hi).2 (hE i hi)
      calc
        F*Q = pptFullComparisonPrefactor C (B z) (b i) d.primeFactorsList.length
            (h i) (Real.log (Y i (b i))) (B (V i)) M*(Real.log z)^E := by
          dsimp only [F, Q, pptFullComparisonPrefactor]
          ring
        _ ≤ L := hh
    have hscale : 0 ≤ pptComparisonScale C (b i) z (W i) (Y i) (U i) :=
      ppt_comparison_scale_nonneg hC.le hB.le hz.le (hY i hi).1.le
    have hcore : ((T i).card : ℝ) ≤
        (z/(d : ℝ))*((1/((a i).totient : ℝ))*(1/((c i).totient : ℝ)))*F := by
      have hraw := hcount (b i) d (c i) (a i) z (W i) (Y i) (U i)
        hz₀ (hparams i hi) (T i) (t i) (hreal i hi) (hconditions i hi)
      rw [ppt_comparison_bound_factor] at hraw
      have hmul := mul_le_mul_of_nonneg_left hcost
        (show 0 ≤ z/(d : ℝ)*pptComparisonScale C (b i) z (W i) (Y i) (U i)*
          (1/((c i).totient : ℝ))*(1/((a i).totient : ℝ)) by positivity)
      apply hraw.trans (hmul.trans_eq _)
      dsimp only [F, pptComparisonScale, E]
      ring
    calc
      ((T i).card : ℝ)*Q ≤
          ((z/(d : ℝ))*((1/((a i).totient : ℝ))*(1/((c i).totient : ℝ)))*F)*Q :=
        mul_le_mul_of_nonneg_right hcore hQ.le
      _ = (z/(d : ℝ))*((1/((a i).totient : ℝ))*(1/((c i).totient : ℝ)))*(F*Q) := by ring
      _ ≤ (z/(d : ℝ))*((1/((a i).totient : ℝ))*(1/((c i).totient : ℝ)))*L :=
        mul_le_mul_of_nonneg_left hsaved (by positivity)
      _ = _ := by ring
  have hsum : (∑ i ∈ I, ((T i).card : ℝ))*Q ≤ (z/(d : ℝ)*L)*Q := by
    calc
      _ = ∑ i ∈ I, ((T i).card : ℝ)*Q := Finset.sum_mul I _ Q
      _ ≤ ∑ i ∈ I, (z/(d : ℝ)*L)*
          ((1/((a i).totient : ℝ))*(1/((c i).totient : ℝ))) :=
        Finset.sum_le_sum hblock
      _ = (z/(d : ℝ)*L)*(∑ i ∈ I,
          (1/((a i).totient : ℝ))*(1/((c i).totient : ℝ))) := (Finset.mul_sum I _ _).symm
      _ ≤ (z/(d : ℝ)*L)*Q := mul_le_mul_of_nonneg_left hmass hscalar
  have hh := (mul_le_mul_iff_left₀ hQ).mp hsum
  convert hh using 1
  dsimp only [L]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A finite cover by the actual comparison blocks suffices; the blocks
need not be disjoint. -/
lemma ppt_residual_block_cover {α : Type*} [DecidableEq α]
    (I : Finset α) (T : α → Finset ℕ) (R : Finset ℕ) {X : ℝ}
    (hcover : ∀ n ∈ R, ∃ i ∈ I, n ∈ T i)
    (hcount : (∑ i ∈ I, ((T i).card : ℝ)) ≤ X) : (R.card : ℝ) ≤ X := by
  classical
  have hsub : R ⊆ I.biUnion T := by
    intro n hn
    obtain ⟨i, hi, hni⟩ := hcover n hn
    exact Finset.mem_biUnion.mpr ⟨i, hi, hni⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hcr : (R.card : ℝ) ≤ ∑ i ∈ I, ((T i).card : ℝ) := by
    exact_mod_cast hc
  exact hcr.trans hcount

end TotientAsymptotic

end

end OAI
