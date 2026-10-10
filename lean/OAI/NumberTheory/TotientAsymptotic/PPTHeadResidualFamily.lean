import OAI.NumberTheory.TotientAsymptotic.PPTResidualFamily

namespace OAI

/-!
The original-head residual case uses the top simplex inequality. Only
the surviving tail coordinates embed in the geometric vector; the first
prime is handled by the normal large-part condition.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The true top-row exponent saving, including the empty surviving-tail
case `b = 1`. The head is not embedded in the tail vector. -/
theorem ppt_head_pair_exponent {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n b H : ℕ) (budget c S e w δ : ℝ)
      (t : ShiftedPair b) (v : Fin n → ℝ) (ι : Fin (b-1) ↪o Fin n) (ν μ : ℕ → ℝ),
      ∀ hb : 0 < b,
      v ∈ relaxedGeometricFamily m n budget c → (∀ i, 3 ≤ t.left i) →
      budget ≤ B z+1 →
      (∀ r : Fin (b-1), v (ι r) = B (t.left ⟨r.val+1,by omega⟩)) →
      1 ≤ H → b ≤ H → m+1 ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      0 ≤ δ → δ ≤ 2*((Real.log (B z))^5/Real.sqrt (B z)) →
      e ≤ (2*(b : ℝ)+4)*δ → w ≤ (4*(b : ℝ)+3)*δ → Real.sqrt (B S/B z) ≤ δ →
      (∀ i : Fin b, 0 < i.val → ν i ≤ B (largestPrimeFactor (t.left i-1))/B z+e) →
      (∀ i ∈ Finset.Icc 1 (b-1), ν i-μ i ≤ w) →
      -2+(∑ i ∈ Finset.Icc 1 (b-1), a i*(B (comparisonCutoffs z ν i)/B z))+
        comparisonError b z S (comparisonCutoffs z ν) (comparisonCutoffs z μ) ≤
        -1-(1/(80*A^3))/(Real.log (B z))^3 := by
  filter_upwards [B_tendsto.eventually (ppt_local_head_error_absorbed hA (by norm_num : (0 : ℝ) ≤ 1)),
    B_tendsto.eventually (ppt_grid_error_absorbed_two_mesh hA),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with z hheaderr hgriderr hB
  intro m n b H budget c S e w δ t v ι ν μ hb hv hp3 hbudget hcoords
    hH hbH hmH hdim hδ hδmax he hw hη hν hwidth
  have hB0 : 0 < B z := zero_lt_one.trans hB
  have hround (r : Fin (b-1)) : ν (r.val+1) ≤ v (ι r)/B z+e := by
    let i : Fin b := ⟨r.val+1,by omega⟩
    have hl : (1 : ℝ) < largestPrimeFactor (t.left i-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ t.left i-1 by have := hp3 i; omega)
    have hnat : largestPrimeFactor (t.left i-1) ≤ t.left i :=
      (largestPrimeFactor_le_self (by have := hp3 i; omega)).trans (Nat.sub_le _ _)
    have hmono : B (largestPrimeFactor (t.left i-1)) ≤ B (t.left i) :=
      Real.log_le_log (Real.log_pos hl)
        (Real.log_le_log (zero_lt_one.trans hl) (Nat.cast_le.mpr hnat))
    have hh := div_le_div_of_nonneg_right hmono hB0.le
    have hri := hν i (by dsimp only [i]; omega)
    rw [hcoords r]
    change ν i.val ≤ B (t.left i)/B z+e
    linarith only [hri, hh]
  have hrow := ppt_relaxed_surviving_top_exponent hv ι ν μ hB0 hB0.ne' hbudget
    (hheaderr H m hdim hmH) hround hwidth
    (hgriderr b H m e w (Real.sqrt (B S/B z)) δ
      hH hbH hmH hdim hδ hδmax he hw hη)
  have hsaving := ppt_residual_inverse_log_saving hA (Real.log_pos hB) hmH hdim
  linarith only [hrow, hsaving]

/-- An original-head residual family has the saved comparison bound
from its actual prime lists and geometric rows.  The explicit arithmetic
conditions are supplied after the square and nonnormal preimages have
been removed.  No comparison-condition or exponent conclusion is an
assumption of this application theorem. -/
theorem ppt_head_residual_block_decay (d : ℕ) (hd : 0 < d)
    {A : ℝ} (hA : 0 < A) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m N b h H c a : ℕ) (budget g W V e w δ : ℝ) (ν μ : ℕ → ℝ)
      (tail : Fin h → ℕ) (T : Finset ℕ) (t : ℕ → ShiftedPair b),
      ∀ hb : 1 ≤ b, 1 ≤ H → b ≤ H → h ≤ H → m+1 ≤ H →
      budget ≤ B z+1 → (H : ℝ) ≤ A*Real.log (B z) →
      1 < W → 0 ≤ B W → W ≤ V → W ≤ z →
      B (comparisonCutoffs z ν b) ≤ 2*(B z)^(2/3 : ℝ) →
      0 ≤ B V → B V ≤ 2*(B z)^(2/3 : ℝ) →
      a = ∏ i, tail i → Function.Injective tail →
      (∀ i, IsNormalPrime W (tail i)) →
      (∀ i, (largestPrimeFactor (tail i-1) : ℝ) ≤ V) →
      0 ≤ δ → δ ≤ 2*((Real.log (B z))^5/Real.sqrt (B z)) →
      e ≤ (2*(b : ℝ)+4)*δ → w ≤ (4*(b : ℝ)+3)*δ → Real.sqrt (B W/B z) ≤ δ →
      (∀ i ∈ Finset.Icc 1 (b-1), ν i-μ i ≤ w) →
      FordComparisonParameters b z W (d*a.totient) c.totient
        (comparisonCutoffs z ν) (comparisonCutoffs z μ) →
      (∀ n ∈ T, n = c*a*∏ i, (t n).left i) →
      (∀ n ∈ T, ∀ i,
        IsNormalPrime W ((t n).left i) ∧ IsNormalPrime W ((t n).right i) ∧
        3 ≤ (t n).left i ∧ 3 ≤ (t n).right i ∧ (t n).left i ≠ (t n).right i) →
      (∀ n ∈ T, 0 < (t n).remainder) →
      (∀ n ∈ T, (d*a.totient)*shiftedProduct (t n).left =
        (t n).remainder*shiftedProduct (t n).right) →
      (∀ n ∈ T, (((d*a.totient)*shiftedProduct (t n).left : ℕ) : ℝ) ≤ z/c.totient) →
      (∀ n ∈ T, SquarefreeAbove ((d*a.totient)*shiftedProduct (t n).left)
        (comparisonCutoffs z ν b)) →
      (∀ n ∈ T, (largestPrimeFactor (t n).remainder : ℝ) ≤ comparisonCutoffs z ν b) →
      (∀ n ∈ T, ∀ i : Fin b,
        μ i ≤ B (largestPrimeFactor ((t n).left i-1))/B z ∧
        B (largestPrimeFactor ((t n).left i-1))/B z ≤ ν i ∧
        μ i ≤ B (largestPrimeFactor ((t n).right i-1))/B z ∧
        B (largestPrimeFactor ((t n).right i-1))/B z ≤ ν i) →
      (∀ n ∈ T, ∀ hb : 0 < b, z^(9/10 : ℝ) ≤ (t n).left ⟨0,hb⟩ ∧
        ((t n).left ⟨0,hb⟩-1 : ℕ) ≤ z) →
      (∀ n ∈ T, ∀ i : Fin b, 0 < i.val →
        ν i ≤ B (largestPrimeFactor ((t n).left i-1))/B z+e) →
      (∀ n ∈ T, ∃ (v : Fin N → ℝ) (ι : Fin (b-1) ↪o Fin N),
        v ∈ relaxedGeometricFamily m N budget g ∧
        ∀ r : Fin (b-1), v (ι r) = B ((t n).left ⟨r.val+1,by omega⟩)) →
      (T.card : ℝ) ≤
        (z/((d : ℝ)*Real.log z)*(B z)^(-K))*(1/(a.totient : ℝ))*(1/(c.totient : ℝ)) := by
  have hγ : 0 < 1/(80*A^3) := by positivity
  filter_upwards [ppt_normal_tail_fixed_block_decay d hd hA.le hγ K,
    ppt_head_pair_exponent hA, ppt_normalized_pair_conditions,
    eventually_gt_atTop (1 : ℝ), B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with z hcount hexponent hconditions hz hB
  intro m N b h H c a budget g W V e w δ ν μ tail T t hb hH hbH hhH hmH hbudget hdim
    hW hBW hWV hWz hBY hV0 hV htail hinj hnormal hsmall hδ hδmax he hw hη hwidth
    hparams hreal hprime hrem heq hsize hsq hEs hinterval hhead hround hgeom
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hbdim : (b : ℝ) ≤ A*Real.log (B z) := (Nat.cast_le.mpr hbH).trans hdim
  have hhdim : (h : ℝ) ≤ A*Real.log (B z) := (Nat.cast_le.mpr hhH).trans hdim
  have hYb : 1 < comparisonCutoffs z ν b := Real.one_lt_exp_iff.mpr (Real.exp_pos _)
  have hY1 : 1 ≤ comparisonCutoffs z ν 1 :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos _)).le
  by_cases hT : T.Nonempty
  · obtain ⟨n, hn⟩ := hT
    obtain ⟨v, ι, hv, hcoords⟩ := hgeom n hn
    have hE := hexponent m N b H budget g W e w δ (t n) v ι ν μ hb0 hv
      (fun i => (hprime n hn i).2.2.1) hbudget hcoords
      hH hbH hmH hdim hδ hδmax he hw hη (hround n hn) hwidth
    apply hcount b h c a W V (comparisonCutoffs z ν) (comparisonCutoffs z μ)
      tail T t hb hbdim hhdim hW hBW hWV hYb hBY hV0 hV htail hinj hnormal hsmall
      hE hparams hreal
    intro n hn
    exact hconditions b (d*a.totient) c.totient W ν μ (t n) hb0 hB hW hBW hWz
      (fun i => (hprime n hn i).1) (fun i => (hprime n hn i).2.1)
      (fun i => (hprime n hn i).2.2.1) (fun i => (hprime n hn i).2.2.2.1)
      (fun i => (hprime n hn i).2.2.2.2) (hrem n hn) (heq n hn) (hsize n hn)
      (hsq n hn) (hEs n hn) (hinterval n hn) (hhead n hn hb0).1 (hhead n hn hb0).2
      hY1 hparams.2.2.2.2.2.1
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    rw [hTempty, Finset.card_empty, Nat.cast_zero]
    have hz0 : 0 < z := zero_lt_one.trans hz
    have hlogz : 0 < Real.log z := Real.log_pos hz
    positivity


end TotientAsymptotic

end

end OAI
