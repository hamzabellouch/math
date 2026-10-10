import OAI.NumberTheory.JointDickman.Arithmetic.NumericSieveError
import OAI.NumberTheory.JointDickman.Amplification.LowNumericAdditionBound
import OAI.NumberTheory.JointDickman.Amplification.LargeNumericAddition
import OAI.NumberTheory.JointDickman.Amplification.NumericRankinExponent

namespace OAI

/-! # The large low-endpoint numeric-addition harmonic estimate -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- Equation (28) of the manuscript, for a positive lag and the designated
large addition at its low endpoint.  The explicit sieve remainder has been
absorbed uniformly in the cardinality class. -/
theorem large_low_numeric_addition_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g κ Δ δ ε : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hκ : 0 < κ) (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (τ C : ℝ) (e j b d : ℕ) (W : ℝ), 0 ≤ τ → τ ≤ 1 →
        0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B → e.Coprime j →
        (e*b : ℕ) ≤ Real.exp (κ*B) → (j : ℝ) ≤ (B : ℝ)^2 →
        2*(j : ℝ) ≤ W → Real.exp ((B : ℝ)^(g-Δ))/4 ≤ W →
        (∑ Z ∈ lowNumericAdditionClass B L τ C e j b d W,
          (1/2 : ℝ)^d/((∏ p ∈ Z, p : ℕ) : ℝ)) ≤
          K/(j : ℝ)*Real.exp
            (largeAdditionExponent g Δ δ τ ε (auxiliaryLogLength B) d*auxiliaryLogLength B) := by
  have hγ : 0 < g-2*Δ := by linarith
  have hγ1 : g-2*Δ < 1 := by linarith
  have ha : 0 < g-Δ := by linarith
  have hγa : g-2*Δ < g-Δ := by linarith
  obtain ⟨K,hK,hbound⟩ := low_numeric_addition_class_bound hFord hM hκ hγ hγ1 hε
  refine ⟨K+1,by positivity,?_⟩
  filter_upwards [hbound,numeric_sieve_remainder_small ha hγa 10,
    auxiliaryLogLength_tendsto.eventually_gt_atTop 0,
    auxiliaryLogLength_between,eventually_gt_atTop 1] with B hB herr hℓ hℓB hB1
  intro τ C e j b d W hτ hτ1 he hb hj hcut hej hsize hjB hW hWlarge
  let ℓ := auxiliaryLogLength B
  let x := (d : ℝ)/(g*ℓ)
  let r := min x (1/2)
  let q := max δ r
  let A := largeAdditionExponent g Δ δ τ ε ℓ d
  let P := ((1/2 : ℝ)/q)^d*Real.exp (((g/2+τ)*ℓ)*Real.log 2)
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hBr : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hx : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) (mul_pos hg hℓ).le
  have hr : 0 ≤ r := le_min hx (by norm_num)
  have hr1 : r ≤ 1/2 := min_le_right _ _
  have hq : 0 < q := hδ.trans_le (le_max_left _ _)
  have hq1 : q ≤ 1/2 := max_le hδ1 hr1
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hPsmall : P ≤ Real.exp (3*ℓ) := numeric_rankin_prefactor_bound hg hg1 hℓ hτ1 hδ hδ1
  have hclass := hB L k τ C e j b d q W hk (by rw [hkg]; linarith)
    he hb hj hcut hej hsize hq (by linarith) hW
  rw [hkg] at hclass
  change (∑ Z ∈ lowNumericAdditionClass B L τ C e j b d W,
    (1/2 : ℝ)^d/((∏ p ∈ Z, p : ℕ) : ℝ)) ≤
      P*(K/(j : ℝ)*Real.exp ((-(3/2-q)*(g-2*Δ)+ε)*ℓ)+_) at hclass
  have hmain : P*Real.exp ((-(3/2-q)*(g-2*Δ)+ε)*ℓ) ≤ Real.exp (A*ℓ) := by
    have hpow : ((1/2 : ℝ)/q)^d = Real.exp ((d : ℝ)*Real.log ((1/2 : ℝ)/q)) := by
      rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
    have hxid : g*ℓ*x = (d : ℝ) := by dsimp only [x]; field_simp [hg.ne',show ℓ ≠ 0 from hℓ.ne']
    have hexp := numeric_rankin_exponent_bound (τ := τ) hg.le (by linarith : g-2*Δ ≤ g) hx hδ hδ1
    change -(3/2-q)*(g-2*Δ)+g*x*Real.log ((1/2)/q)+(g/2+τ)*Real.log 2 ≤ _ at hexp
    have hgδ := mul_le_mul_of_nonneg_right hg1 hδ.le
    have hcoef : -(3/2-q)*(g-2*Δ)+g*x*Real.log ((1/2)/q)+(g/2+τ)*Real.log 2+ε ≤ A := by
      dsimp only [A,largeAdditionExponent,r] at *
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef hℓ.le
    dsimp only [P]
    rw [hpow,← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hexact : (d : ℝ)*Real.log ((1/2)/q)+((g/2+τ)*ℓ)*Real.log 2+
        (-(3/2-q)*(g-2*Δ)+ε)*ℓ =
        (-(3/2-q)*(g-2*Δ)+g*x*Real.log ((1/2)/q)+(g/2+τ)*Real.log 2+ε)*ℓ := by
      calc
        _ = (g*ℓ*x)*Real.log ((1/2)/q)+((g/2+τ)*ℓ)*Real.log 2+
          (-(3/2-q)*(g-2*Δ)+ε)*ℓ := by rw [hxid]
        _ = _ := by ring
    rwa [hexact]
  have hA : -2 ≤ A := by
    have hF := halfRankinExponent_nonneg hr hr1
    have hbase : weightBaseExponent ≤ 1/2 := by
      unfold weightBaseExponent
      have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      linarith
    have hlog : 0 ≤ τ*Real.log 2 := mul_nonneg hτ (Real.log_nonneg (by norm_num))
    have hh : -2 ≤ g*(halfRankinExponent r-1-weightBaseExponent) := by
      have hp := mul_nonneg hg.le hF
      have hb' : g*weightBaseExponent ≤ g*(1/2) := mul_le_mul_of_nonneg_left hbase hg.le
      nlinarith
    dsimp only [A,largeAdditionExponent]
    change -2 ≤ g*(halfRankinExponent r-1-weightBaseExponent)+3*Δ+δ+τ*Real.log 2+ε
    linarith
  have hW0 : 0 < W := by linarith
  have herr' := herr j W hj hjB hWlarge
  have herrfinal : P*(4*(numericAdditionSieveCutoff B (g-2*Δ)+1 : ℝ)*
      (numericAdditionSieveCutoff B (g-2*Δ) : ℝ)^2/W) ≤ Real.exp (A*ℓ)/(j : ℝ) := by
    calc
      _ ≤ Real.exp (3*ℓ)*((B : ℝ)^(-(10 : ℝ))/(j : ℝ)) :=
        mul_le_mul hPsmall herr' (by positivity) (Real.exp_pos _).le
      _ = Real.exp (3*ℓ-10*Real.log B)/(j : ℝ) := by
        rw [Real.rpow_def_of_pos hBr,← mul_div_assoc,← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hjr.le
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_right hA hℓ.le
        have hupper : ℓ ≤ Real.log B := hℓB.2
        linarith
  refine hclass.trans ?_
  rw [mul_add]
  calc
    _ = K/(j : ℝ)*(P*Real.exp ((-(3/2-q)*(g-2*Δ)+ε)*ℓ))+
        P*(4*(numericAdditionSieveCutoff B (g-2*Δ)+1 : ℝ)*
          (numericAdditionSieveCutoff B (g-2*Δ) : ℝ)^2/W) := by ring
    _ ≤ K/(j : ℝ)*Real.exp (A*ℓ)+Real.exp (A*ℓ)/(j : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain (by positivity)) herrfinal
    _ = _ := by dsimp only [A,ℓ]; ring

end JointDickman

end OAI
