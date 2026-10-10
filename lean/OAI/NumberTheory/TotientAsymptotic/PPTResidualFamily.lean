import OAI.NumberTheory.TotientAsymptotic.PPTGridSeparation
import OAI.NumberTheory.TotientAsymptotic.PPTComparisonBlockDecay

namespace OAI

/-!
Fixed residual families in the PPT pruning argument.  Their members are
actual integers recovered from a common prime product, a small left tail,
and the surviving left prime list.  The counting conclusion retains both
reciprocal totient weights for the subsequent prefix and suffix sums.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma ppt_squarefreeAbove_mono {n : ℕ} {U V : ℝ}
    (hUV : U ≤ V) (hn : SquarefreeAbove n U) : SquarefreeAbove n V := by
  intro p hp hVp
  exact hn p hp (hUV.trans_lt hVp)

/-- After excluding squares above a smaller cutoff, both the actual
preimage and its target totient are squarefree at the comparison cutoff. -/
lemma ppt_squarefree_residual_target {u D : ℕ} {K S Y : ℝ}
    (hKS : K ≤ S) (hKY : K ≤ Y)
    (hu : SquarefreeAbove u K) (hφ : SquarefreeAbove u.totient K)
    (hD : D ∣ u.totient) : SquarefreeAbove u S ∧ SquarefreeAbove D Y :=
  ⟨ppt_squarefreeAbove_mono hKS hu,
    squarefreeAbove_of_dvd hD (ppt_squarefreeAbove_mono hKY hφ)⟩

/-- The literal pointwise comparison conditions for an already canceled
pair follow from its arithmetic equation and normalized factor bands.
The large-part condition is proved from the actual left head. -/
theorem ppt_normalized_pair_conditions : ∀ᶠ z : ℝ in atTop,
    ∀ (b D r : ℕ) (S : ℝ) (ν μ : ℕ → ℝ) (t : ShiftedPair b),
      ∀ hb : 0 < b,
      0 < B z → 1 < S → 0 ≤ B S → S ≤ z →
      (∀ i, IsNormalPrime S (t.left i)) →
      (∀ i, IsNormalPrime S (t.right i)) →
      (∀ i, 3 ≤ t.left i) → (∀ i, 3 ≤ t.right i) →
      (∀ i, t.left i ≠ t.right i) →
      0 < t.remainder → D*shiftedProduct t.left = t.remainder*shiftedProduct t.right →
      ((D*shiftedProduct t.left : ℕ) : ℝ) ≤ z/r →
      SquarefreeAbove (D*shiftedProduct t.left) (comparisonCutoffs z ν b) →
      (largestPrimeFactor t.remainder : ℝ) ≤ comparisonCutoffs z ν b →
      (∀ i : Fin b,
        μ i ≤ B (largestPrimeFactor (t.left i-1))/B z ∧
        B (largestPrimeFactor (t.left i-1))/B z ≤ ν i ∧
        μ i ≤ B (largestPrimeFactor (t.right i-1))/B z ∧
        B (largestPrimeFactor (t.right i-1))/B z ≤ ν i) →
      z^(9/10 : ℝ) ≤ t.left ⟨0,hb⟩ → (t.left ⟨0,hb⟩-1 : ℕ) ≤ z →
      1 ≤ comparisonCutoffs z ν 1 →
      comparisonCutoffs z ν 1 ≤ z^(1/(10*B z)) →
      FordComparisonConditions b z S D r
        (comparisonCutoffs z ν) (comparisonCutoffs z μ) t := by
  filter_upwards [ppt_normal_comparison_large_part] with z hlarge
  intro b D r S ν μ t hb hB hS hBS hSz hp hq hp3 hq3 hne hE heq hsize
    hsq hEs hinterval hhead hpz hY hYpower
  refine ⟨hE, ?_, heq, hsize, hEs, ?_, ?_⟩
  · intro i
    have hpone : (1 : ℝ) < largestPrimeFactor (t.left i-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ t.left i-1 by have := hp3 i; omega)
    have hqone : (1 : ℝ) < largestPrimeFactor (t.right i-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ t.right i-1 by have := hq3 i; omega)
    have hpi := ppt_normalized_factor_interval hB hpone (hinterval i).1 (hinterval i).2.1
    have hqi := ppt_normalized_factor_interval hB hqone (hinterval i).2.2.1 (hinterval i).2.2.2
    have hsides := squarefree_shifts_of_common_product t (comparisonCutoffs z ν b) heq hsq i
    exact ⟨hp i, hq i, hne i, hpi.1, hpi.2, hqi.1, hqi.2, hsides.1, hsides.2⟩
  · intro hb'
    exact hlarge (t.left ⟨0,hb'⟩) S (comparisonCutoffs z ν 1)
      hS hBS hSz (hp _) hhead hpz hY hYpower
  · exact squarefreeAbove_of_dvd (dvd_mul_left _ _) hsq

/-- The exponent of an already canceled pair is controlled by its
actual embedding in the constructed geometric candidate family. -/
theorem ppt_geometric_pair_exponent {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n b H : ℕ) (budget c S e w δ : ℝ)
      (t : ShiftedPair b) (v : Fin n → ℝ) (ι : Fin b ↪o Fin n) (ν μ : ℕ → ℝ),
      ∀ hb : 0 < b,
      v ∈ relaxedGeometricFamily m n budget c → (∀ i, 3 ≤ t.left i) →
      (t.left ⟨0,hb⟩-1 : ℕ) ≤ z → (∀ i, v (ι i) = B (t.left i)) →
      1 ≤ H → b ≤ H → m-((ι ⟨0,hb⟩).val+1)+1 ≤ H →
      (H : ℝ) ≤ A*Real.log (B z) →
      0 ≤ δ → δ ≤ 2*((Real.log (B z))^5/Real.sqrt (B z)) →
      e ≤ (2*(b : ℝ)+4)*δ → w ≤ (4*(b : ℝ)+3)*δ → Real.sqrt (B S/B z) ≤ δ →
      (∀ i : Fin b, 0 < i.val → ν i ≤ B (largestPrimeFactor (t.left i-1))/B z+e) →
      (∀ i ∈ Finset.Icc 1 (b-1), ν i-μ i ≤ w) →
      -2+(∑ i ∈ Finset.Icc 1 (b-1), a i*(B (comparisonCutoffs z ν i)/B z))+
        comparisonError b z S (comparisonCutoffs z ν) (comparisonCutoffs z μ) ≤
        -1-(1/(80*A^3))/(Real.log (B z))^3 := by
  filter_upwards [B_tendsto.eventually (ppt_local_head_error_absorbed hA (by norm_num : (0 : ℝ) ≤ 1)),
    B_tendsto.eventually (ppt_grid_error_absorbed_two_mesh hA),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_ge_atTop (Real.exp 1)] with z hheaderr hgriderr hB hz
  intro m n b H budget c S e w δ t v ι ν μ hb hv hp3 hpz hcoords
    hH hbH hrH hdim hδ hδmax he hw hη hν hwidth
  have hB0 : 0 < B z := zero_lt_one.trans hB
  have hhead : v (ι ⟨0,hb⟩) ≤ B z+1 := by
    rw [hcoords]
    exact prime_coordinate_endpoint_bound (hp3 _) hz hpz
  have hround (i : Fin b) (hi : 0 < i.val) : ν i ≤ v (ι i)/B z+e := by
    have hl : (1 : ℝ) < largestPrimeFactor (t.left i-1) := by
      exact_mod_cast one_lt_largestPrimeFactor (show 2 ≤ t.left i-1 by have := hp3 i; omega)
    have hnat : largestPrimeFactor (t.left i-1) ≤ t.left i :=
      (largestPrimeFactor_le_self (by have := hp3 i; omega)).trans (Nat.sub_le _ _)
    have hmono : B (largestPrimeFactor (t.left i-1)) ≤ B (t.left i) :=
      Real.log_le_log (Real.log_pos hl)
        (Real.log_le_log (zero_lt_one.trans hl) (Nat.cast_le.mpr hnat))
    have hh := div_le_div_of_nonneg_right hmono hB0.le
    rw [← hcoords i] at hh
    apply (hν i hi).trans
    linarith only [hh]
  have hrow := ppt_relaxed_surviving_exponent hv ι hb ν μ hB0 hB0.ne' hhead
    (hheaderr H (m-((ι ⟨0,hb⟩).val+1)) hdim hrH) hround hwidth
    (hgriderr b H (m-((ι ⟨0,hb⟩).val+1)) e w (Real.sqrt (B S/B z)) δ
      hH hbH hrH hdim hδ hδmax he hw hη)
  have hsaving := ppt_residual_inverse_log_saving hA (Real.log_pos hB) hrH hdim
  linarith only [hrow, hsaving]

/-- The published comparison bound on a fixed residual family has an
arbitrary inverse-power saving, with both fixed-factor weights retained.
There is no assumed estimate for the family cardinality. -/
theorem ppt_normal_tail_fixed_block_decay (d : ℕ) (hd : 0 < d)
    {A γ : ℝ} (hA : 0 ≤ A) (hγ : 0 < γ) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (b h c a : ℕ) (W V : ℝ) (Y U : ℕ → ℝ)
      (tail : Fin h → ℕ) (T : Finset ℕ) (t : ℕ → ShiftedPair b),
      1 ≤ b → (b : ℝ) ≤ A*Real.log (B z) → (h : ℝ) ≤ A*Real.log (B z) →
      1 < W → 0 ≤ B W → W ≤ V → 1 < Y b →
      B (Y b) ≤ 2*(B z)^(2/3 : ℝ) → 0 ≤ B V → B V ≤ 2*(B z)^(2/3 : ℝ) →
      a = ∏ i, tail i → Function.Injective tail →
      (∀ i, IsNormalPrime W (tail i)) →
      (∀ i, (largestPrimeFactor (tail i-1) : ℝ) ≤ V) →
      -2+(∑ j ∈ Finset.Icc 1 (b-1), TotientAsymptotic.a j*(B (Y j)/B z))+
        comparisonError b z W Y U ≤ -1-γ/(Real.log (B z))^3 →
      FordComparisonParameters b z W (d*a.totient) c.totient Y U →
      (∀ n ∈ T, n = c*a*∏ i, (t n).left i) →
      (∀ n ∈ T, FordComparisonConditions b z W (d*a.totient) c.totient Y U (t n)) →
      (T.card : ℝ) ≤
        (z/((d : ℝ)*Real.log z)*(B z)^(-K))*(1/(a.totient : ℝ))*(1/(c.totient : ℝ)) := by
  obtain ⟨C, z₀, hC, _, hcount⟩ := ppt_plain_comparison_block_count
  filter_upwards [ppt_full_comparison_decay (M := 0) hC hA hγ d.primeFactorsList.length K,
    eventually_ge_atTop z₀, eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with z hdecay hz₀ hz hB
  intro b h c a W V Y U tail T t hb hbL hhL hW hBW hWV hY hBY hV0 hV
    htail hinj hnormal hsmall hE hparams hreal hconditions
  have hcost : (b+1 : ℝ)^((d*a.totient).primeFactorsList.length) ≤
      (b+1 : ℝ)^d.primeFactorsList.length *
        Real.exp (4*(h : ℝ)*B V*Real.log (b+1)) := by
    rw [htail]
    exact ppt_small_tail_comparison_cost b tail hd hnormal hinj hW hBW hWV hsmall
  let E : ℝ := -2+(∑ j ∈ Finset.Icc 1 (b-1), TotientAsymptotic.a j*(B (Y j)/B z))+
    comparisonError b z W Y U
  let F : ℝ := (C*B z)^(6*b)*(Real.log (Y b))^(20*(b : ℝ)*Real.log b+1)*
    (b+1 : ℝ)^d.primeFactorsList.length *
    Real.exp (4*(h : ℝ)*B V*Real.log (b+1))*(Real.log z)^E
  have hsaved : F ≤ (Real.log z)⁻¹*(B z)^(-K) := by
    have hh := hdecay b h (Real.log (Y b)) (B V) E hb hbL hhL
      (Real.log_pos hY) hBY hV0 hV hE
    simpa only [pptFullComparisonPrefactor, zero_mul, Real.exp_zero, mul_one, F] using hh
  have hscale : 0 ≤ pptComparisonScale C b z W Y U :=
    ppt_comparison_scale_nonneg hC.le hB.le hz.le hY.le
  let Q : ℝ := z/(d : ℝ)*(1/(c.totient : ℝ))*(1/(a.totient : ℝ))
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have hcore : fordComparisonBound C b z W (d*a.totient) c.totient Y U ≤ Q*F := by
    rw [ppt_comparison_bound_factor]
    have hmul := mul_le_mul_of_nonneg_left hcost
      (show 0 ≤ z/(d : ℝ)*pptComparisonScale C b z W Y U*
        (1/(c.totient : ℝ))*(1/(a.totient : ℝ)) by positivity)
    apply hmul.trans_eq
    dsimp only [Q, F, pptComparisonScale, E]
    ring
  calc
    (T.card : ℝ) ≤ fordComparisonBound C b z W (d*a.totient) c.totient Y U :=
      hcount b d c a z W Y U hz₀ hparams T t hreal hconditions
    _ ≤ Q*F := hcore
    _ ≤ Q*((Real.log z)⁻¹*(B z)^(-K)) := mul_le_mul_of_nonneg_left hsaved hQ
    _ = _ := by
      dsimp only [Q]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- A finite late-prefix residual family has the saved comparison bound
from its actual prime lists and geometric rows.  The explicit arithmetic
conditions are supplied after the square and nonnormal preimages have
been removed.  No comparison-condition or exponent conclusion is an
assumption of this application theorem. -/
theorem ppt_geometric_residual_block_decay (d : ℕ) (hd : 0 < d)
    {A : ℝ} (hA : 0 < A) (K : ℝ) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m N b h H c a : ℕ) (budget g W V e w δ : ℝ) (ν μ : ℕ → ℝ)
      (tail : Fin h → ℕ) (T : Finset ℕ) (t : ℕ → ShiftedPair b),
      1 ≤ b → 1 ≤ H → b ≤ H → h ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
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
      (∀ n ∈ T, ∃ (v : Fin N → ℝ) (ι : Fin b ↪o Fin N),
        v ∈ relaxedGeometricFamily m N budget g ∧ (∀ i, v (ι i) = B ((t n).left i)) ∧
        ∀ hb : 0 < b, m-((ι ⟨0,hb⟩).val+1)+1 ≤ H) →
      (T.card : ℝ) ≤
        (z/((d : ℝ)*Real.log z)*(B z)^(-K))*(1/(a.totient : ℝ))*(1/(c.totient : ℝ)) := by
  have hγ : 0 < 1/(80*A^3) := by positivity
  filter_upwards [ppt_normal_tail_fixed_block_decay d hd hA.le hγ K,
    ppt_geometric_pair_exponent hA, ppt_normalized_pair_conditions,
    eventually_gt_atTop (1 : ℝ), B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with z hcount hexponent hconditions hz hB
  intro m N b h H c a budget g W V e w δ ν μ tail T t hb hH hbH hhH hdim
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
    obtain ⟨v, ι, hv, hcoords, hrow⟩ := hgeom n hn
    have hE := hexponent m N b H budget g W e w δ (t n) v ι ν μ hb0 hv
      (fun i => (hprime n hn i).2.2.1) (hhead n hn hb0).2 hcoords
      hH hbH (hrow hb0) hdim hδ hδmax he hw hη (hround n hn) hwidth
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
