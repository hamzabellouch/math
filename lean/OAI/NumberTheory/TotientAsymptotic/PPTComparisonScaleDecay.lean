import OAI.NumberTheory.TotientAsymptotic.PPTComparisonAssembly
import OAI.NumberTheory.TotientAsymptotic.PPTComparisonDecay

namespace OAI

/-!
The literal Ford comparison prefactor in the PPT range.  The number of
high and low primes is logarithmic in `t`; the terminal cutoff has
double logarithm at most `2 t^(2/3)`.  All fixed-seed and finite-family
costs are retained before applying the proved strict-exponent decay.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def pptFullComparisonPrefactor (C t : ℝ) (b D h : ℕ) (u V M : ℝ) : ℝ :=
  (C*t)^(6*b)*u^(20*(b : ℝ)*Real.log b+1)*(b+1 : ℝ)^D*
    Real.exp (4*(h : ℝ)*V*Real.log (b+1))*Real.exp (M*(Real.log t)^2)

def pptPrefactorConstant (C A M : ℝ) (D : ℕ) : ℝ :=
  6*A*(|Real.log C|+1)+48*A^2+(D : ℝ)*A+2+|M|

private lemma ppt_log_prefactor_bound {A L R X V M : ℝ} {b D h : ℕ}
    (hA : 0 ≤ A) (hL : 1 ≤ L) (hR : 1 ≤ R) (hb : 1 ≤ b)
    (hbL : (b : ℝ) ≤ A*L) (hhL : (h : ℝ) ≤ A*L)
    (hX : X ≤ 2*R) (hV0 : 0 ≤ V) (hV : V ≤ 2*R) :
    6*(b : ℝ)*(M+L)+(20*(b : ℝ)*Real.log b+1)*X+
      (D : ℝ)*Real.log (b+1)+4*(h : ℝ)*V*Real.log (b+1) ≤
        (6*A*(|M|+1)+48*A^2+(D : ℝ)*A+2)*R*L^2 := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hlogb : Real.log b ≤ A*L := (Real.log_le_self hb0).trans hbL
  have hlogb1 : Real.log (b+1) ≤ A*L := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < b+1 by positivity)
    have hh' : Real.log (b+1) ≤ (b : ℝ) := by linarith only [hh]
    exact hh'.trans hbL
  have hlogb10 : 0 ≤ Real.log (b+1) :=
    Real.log_nonneg (show (1 : ℝ) ≤ (b : ℝ)+1 by linarith only [hb0])
  have hAL : 0 ≤ A*L := mul_nonneg hA hL0
  have hpair : (b : ℝ)*Real.log b ≤ A^2*L^2 := by
    have hh := mul_le_mul hbL hlogb hlogb0 hAL
    convert hh using 1
    ring_nf
  have hpair' : (h : ℝ)*Real.log (b+1) ≤ A^2*L^2 := by
    have hh := mul_le_mul hhL hlogb1 hlogb10 hAL
    convert hh using 1
    ring_nf
  have hLL : L ≤ L^2 := by nlinarith only [hL]
  have hRR : L^2 ≤ R*L^2 := by nlinarith only [hR, sq_nonneg L]
  have hML : M+L ≤ (|M|+1)*L := by
    have hm := mul_le_mul_of_nonneg_left hL (abs_nonneg M)
    nlinarith only [hm, le_abs_self M]
  have hfirst : 6*(b : ℝ)*(M+L) ≤ 6*A*(|M|+1)*R*L^2 := by
    calc
      _ ≤ 6*(b : ℝ)*((|M|+1)*L) :=
        mul_le_mul_of_nonneg_left hML (by positivity)
      _ ≤ 6*(A*L)*((|M|+1)*L) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbL (by norm_num))
          (by positivity)
      _ = 6*A*(|M|+1)*L^2 := by ring_nf
      _ ≤ _ := by
        nlinarith only [mul_le_mul_of_nonneg_left hRR
          (show 0 ≤ 6*A*(|M|+1) by positivity)]
  have hcoef0 : 0 ≤ 20*(b : ℝ)*Real.log b+1 := by positivity
  have hcoef : 20*(b : ℝ)*Real.log b+1 ≤ (20*A^2+1)*L^2 := by
    nlinarith only [hpair, hL, sq_nonneg L]
  have hsecond : (20*(b : ℝ)*Real.log b+1)*X ≤ (40*A^2+2)*R*L^2 := by
    calc
      _ ≤ (20*(b : ℝ)*Real.log b+1)*(2*R) :=
        mul_le_mul_of_nonneg_left hX hcoef0
      _ ≤ ((20*A^2+1)*L^2)*(2*R) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring_nf
  have hthird : (D : ℝ)*Real.log (b+1) ≤ (D : ℝ)*A*R*L^2 := by
    calc
      _ ≤ (D : ℝ)*(A*L) := mul_le_mul_of_nonneg_left hlogb1 (Nat.cast_nonneg _)
      _ ≤ (D : ℝ)*(A*L^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLL hA) (Nat.cast_nonneg _)
      _ = (D : ℝ)*A*L^2 := by ring_nf
      _ ≤ _ := by
        nlinarith only [mul_le_mul_of_nonneg_left hRR
          (show 0 ≤ (D : ℝ)*A by positivity)]
  have hfourth : 4*(h : ℝ)*V*Real.log (b+1) ≤ 8*A^2*R*L^2 := by
    calc
      _ = 4*V*((h : ℝ)*Real.log (b+1)) := by ring_nf
      _ ≤ 4*V*(A^2*L^2) := mul_le_mul_of_nonneg_left hpair' (by positivity)
      _ ≤ 4*(2*R)*(A^2*L^2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by norm_num)) (by positivity)
      _ = _ := by ring_nf
  nlinarith only [hfirst, hsecond, hthird, hfourth]

/-- The complete positive prefactor is at most the required exponential
in `t^(2/3) (log t)^2`, uniformly in both prime-list lengths. -/
theorem ppt_full_prefactor_bound {C A t u V M : ℝ} {b D h : ℕ}
    (hC : 0 < C) (hA : 0 ≤ A) (ht : 1 ≤ Real.log t) (ht0 : 0 < t)
    (hb : 1 ≤ b) (hbL : (b : ℝ) ≤ A*Real.log t)
    (hhL : (h : ℝ) ≤ A*Real.log t) (hu : 0 < u)
    (huT : Real.log u ≤ 2*t^(2/3 : ℝ))
    (hV0 : 0 ≤ V) (hV : V ≤ 2*t^(2/3 : ℝ)) :
    pptFullComparisonPrefactor C t b D h u V M ≤
      Real.exp (pptPrefactorConstant C A M D*t^(2/3 : ℝ)*(Real.log t)^2) := by
  have ht1 : 1 ≤ t := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans
    ((Real.exp_le_exp.mpr ht).trans_eq (Real.exp_log ht0))
  have hR : 1 ≤ t^(2/3 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  have hraw := ppt_log_prefactor_bound (D := D) hA ht hR hb hbL hhL huT hV0 hV
    (M := Real.log C)
  have hmass : M*(Real.log t)^2 ≤ |M| * t^(2/3 : ℝ)*(Real.log t)^2 := by
    have hh := mul_le_mul_of_nonneg_left hR (abs_nonneg M)
    have hm : M ≤ |M| * t^(2/3 : ℝ) :=
      (le_abs_self M).trans (by simpa only [mul_one] using hh)
    exact mul_le_mul_of_nonneg_right hm (sq_nonneg _)
  have hCt : 0 < C*t := mul_pos hC ht0
  have hpower : (C*t)^(6*b) = Real.exp ((6*b : ℕ)*Real.log (C*t)) := by
    rw [Real.exp_nat_mul, Real.exp_log hCt]
  have hseed : (b+1 : ℝ)^D = Real.exp ((D : ℝ)*Real.log (b+1)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < b+1)]
  have heq : pptFullComparisonPrefactor C t b D h u V M =
      Real.exp (6*(b : ℝ)*(Real.log C+Real.log t)+
        (20*(b : ℝ)*Real.log b+1)*Real.log u+(D : ℝ)*Real.log (b+1)+
        4*(h : ℝ)*V*Real.log (b+1)+M*(Real.log t)^2) := by
    rw [pptFullComparisonPrefactor, hpower, Real.rpow_def_of_pos hu, hseed]
    rw [Real.log_mul hC.ne' ht0.ne']
    simp only [Real.exp_add, Nat.cast_mul, Nat.cast_ofNat]
    ring_nf
  rw [heq]
  apply Real.exp_le_exp.mpr
  unfold pptPrefactorConstant
  nlinarith only [hraw, hmass]

/-- The literal prefactor, seed cost, normal-tail cost and finite-family
mass are absorbed by the strict inverse-log-cube exponent saving. -/
theorem ppt_full_comparison_decay {C A γ M : ℝ} (hC : 0 < C) (hA : 0 ≤ A)
    (hγ : 0 < γ) (D : ℕ) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop, ∀ (b h : ℕ) (u V E : ℝ),
      1 ≤ b → (b : ℝ) ≤ A*Real.log (B z) → (h : ℝ) ≤ A*Real.log (B z) →
      0 < u → Real.log u ≤ 2*(B z)^(2/3 : ℝ) →
      0 ≤ V → V ≤ 2*(B z)^(2/3 : ℝ) →
      E ≤ -1-γ/(Real.log (B z))^3 →
      pptFullComparisonPrefactor C (B z) b D h u V M*(Real.log z)^E ≤
        (Real.log z)⁻¹*(B z)^(-K) := by
  filter_upwards [ppt_comparison_exp_decay_at_scale (pptPrefactorConstant C A M D) K hγ,
    B_tendsto.eventually (eventually_gt_atTop (Real.exp 1)),
    eventually_gt_atTop (Real.exp 1)] with z hdecay hB hz
  intro b h u V E hb hbL hhL hu huT hV0 hV hE
  have hB0 : 0 < B z := (Real.exp_pos 1).trans hB
  have hlogB : 1 ≤ Real.log (B z) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hB.le
    simpa only [Real.log_exp] using hh
  have hlogz : 1 ≤ Real.log z := by
    have hh := Real.log_le_log (Real.exp_pos 1) hz.le
    simpa only [Real.log_exp] using hh
  have hpre := ppt_full_prefactor_bound hC hA hlogB hB0 hb hbL hhL hu huT hV0 hV
    (D := D) (M := M)
  have hpow := comparison_log_power_saving hlogz hE
  have hpow0 : 0 ≤ (Real.log z)^E := Real.rpow_nonneg (zero_le_one.trans hlogz) _
  calc
    _ ≤ Real.exp (pptPrefactorConstant C A M D*(B z)^(2/3 : ℝ)*
        (Real.log (B z))^2)*((Real.log z)⁻¹*
          Real.exp (-(γ/(Real.log (B z))^3)*B z)) :=
      mul_le_mul hpre hpow hpow0 (Real.exp_pos _).le
    _ = (Real.log z)⁻¹*Real.exp (pptPrefactorConstant C A M D*(B z)^(2/3 : ℝ)*
        (Real.log (B z))^2-γ*B z/(Real.log (B z))^3) := by
      have he : -(γ/(Real.log (B z))^3)*B z = -(γ*B z/(Real.log (B z))^3) := by ring_nf
      rw [he, Real.exp_neg, Real.exp_sub]
      simp only [div_eq_mul_inv]
      ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (inv_nonneg.mpr (zero_le_one.trans hlogz))

end TotientAsymptotic

end

end OAI
