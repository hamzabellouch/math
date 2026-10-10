import OAI.NumberTheory.TotientAsymptotic.PPTComparisonAssembly
import OAI.NumberTheory.TotientAsymptotic.PPTCoordinateAlignment
import OAI.NumberTheory.TotientAsymptotic.PPTGridMargins
import OAI.NumberTheory.TotientAsymptotic.PPTLocalDimension

namespace OAI

/-!
Pointwise comparison data for a residual PPT collision.  The prime lists
and shifted-product equation are the actual residual ones.  Cancellation
preserves that equation, normality supplies the paired-coordinate error,
and the geometric candidate row supplies the strict comparison exponent.
The squarefree target and the small integer residual remain explicit
arithmetic hypotheses; no counting conclusion is assumed here.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma ppt_normalized_factor_interval {z w l u : ℝ}
    (hz : 0 < B z) (hw : 1 < w)
    (hl : l ≤ B w/B z) (hu : B w/B z ≤ u) :
    Real.exp (Real.exp (B z*l)) ≤ w ∧
      w ≤ Real.exp (Real.exp (B z*u)) := by
  have hwl : B z*l ≤ B w := by
    have hh := (le_div_iff₀ hz).mp hl
    simpa only [mul_comm] using hh
  have hwu : B w ≤ B z*u := by
    have hh := (div_le_iff₀ hz).mp hu
    simpa only [mul_comm] using hh
  have he : Real.exp (Real.exp (B w)) = w := by
    rw [B, Real.exp_log (Real.log_pos hw), Real.exp_log (zero_lt_one.trans hw)]
  exact ⟨(Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hwl)).trans_eq he,
    he.symm.trans_le (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hwu))⟩

/-- Normalized intervals of the actual largest predecessor factors give
the literal published comparison conditions after matching cancellation. -/
theorem ppt_canceled_normalized_conditions : ∀ᶠ z : ℝ in atTop,
    ∀ (k D E : ℕ) (p q : Fin k → ℕ) (S : ℝ) (ν μ : ℕ → ℝ),
      ∀ hk : 0 < k,
      0 < B z → 1 < S → 0 ≤ B S → S ≤ z →
      (∀ i, IsNormalPrime S (p i)) → (∀ i, IsNormalPrime S (q i)) →
      (∀ i, 3 ≤ p i) → (∀ i, 3 ≤ q i) →
      Function.Injective p → p ⟨0,hk⟩ ≠ q ⟨0,hk⟩ →
      0 < E → D*shiftedProduct p = E*shiftedProduct q →
      ((D*shiftedProduct p : ℕ) : ℝ) ≤ z →
      SquarefreeAbove (D*shiftedProduct p)
        (comparisonCutoffs z ν (pptUnequalCoordinates p q).card) →
      (largestPrimeFactor E : ℝ) ≤
        comparisonCutoffs z ν (pptUnequalCoordinates p q).card →
      (∀ i : Fin (pptUnequalCoordinates p q).card,
        μ i ≤ B (largestPrimeFactor (p (pptCoordinateEmbedding p q i)-1))/B z ∧
        B (largestPrimeFactor (p (pptCoordinateEmbedding p q i)-1))/B z ≤ ν i ∧
        μ i ≤ B (largestPrimeFactor (q (pptCoordinateEmbedding p q i)-1))/B z ∧
        B (largestPrimeFactor (q (pptCoordinateEmbedding p q i)-1))/B z ≤ ν i) →
      z^(9/10 : ℝ) ≤ p ⟨0,hk⟩ → (p ⟨0,hk⟩-1 : ℕ) ≤ z →
      1 ≤ comparisonCutoffs z ν 1 →
      comparisonCutoffs z ν 1 ≤ z^(1/(10*B z)) →
      FordComparisonConditions (pptUnequalCoordinates p q).card z S D
        (pptCanceledPrimeProduct p q).totient
        (comparisonCutoffs z ν) (comparisonCutoffs z μ) (pptCanceledPair p q E) := by
  filter_upwards [ppt_canceled_comparison_conditions] with z hz
  intro k D E p q S ν μ hk hB hS hBS hSz hp hq hp3 hq3 hpinj hfirst
    hE heq hsize hsq hEs hinterval hhead hpz hY hYpower
  apply hz k D E p q S (comparisonCutoffs z ν) (comparisonCutoffs z μ) hk
    hS hBS hSz hp hq hpinj hfirst hE heq hsize hsq hEs
  · intro i
    have hpone : (1 : ℝ) < largestPrimeFactor (p (pptCoordinateEmbedding p q i)-1) := by
      exact_mod_cast one_lt_largestPrimeFactor
        (show 2 ≤ p (pptCoordinateEmbedding p q i)-1 by have := hp3 (pptCoordinateEmbedding p q i); omega)
    have hqone : (1 : ℝ) < largestPrimeFactor (q (pptCoordinateEmbedding p q i)-1) := by
      exact_mod_cast one_lt_largestPrimeFactor
        (show 2 ≤ q (pptCoordinateEmbedding p q i)-1 by have := hq3 (pptCoordinateEmbedding p q i); omega)
    have hpint := ppt_normalized_factor_interval hB hpone (hinterval i).1 (hinterval i).2.1
    have hqint := ppt_normalized_factor_interval hB hqone (hinterval i).2.2.1 (hinterval i).2.2.2
    exact ⟨hpint.1, hpint.2, hqint.1, hqint.2⟩
  · exact hhead
  · exact hpz
  · exact hY
  · exact hYpower

/-- Apply normality to the canceled lists themselves.  Thus the error
uses the surviving index, rather than its possibly larger original index. -/
theorem ppt_canceled_normalized_alignment {k D E : ℕ}
    (p q : Fin k → ℕ) {S z : ℝ}
    (hS : 1 < S) (hBS : 0 ≤ B S) (hB : 0 < B z) (hSz : S ≤ z)
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (hpa : StrictAnti p) (hqa : StrictAnti q)
    (heq : D*shiftedProduct p = E*shiftedProduct q)
    (hp3 : ∀ i, 3 ≤ p i) (hq3 : ∀ i, 3 ≤ q i)
    (hpz : ∀ i, (p i-1 : ℕ) ≤ z) (hqz : ∀ i, (q i-1 : ℕ) ≤ z)
    (hDS : ∀ i : Fin (pptUnequalCoordinates p q).card,
      (largestPrimeFactor D : ℝ) ≤
        min ((p (pptCoordinateEmbedding p q i)-1 : ℕ) : ℝ)
          ((q (pptCoordinateEmbedding p q i)-1 : ℕ) : ℝ))
    (hES : ∀ i : Fin (pptUnequalCoordinates p q).card,
      (largestPrimeFactor E : ℝ) ≤
        min ((p (pptCoordinateEmbedding p q i)-1 : ℕ) : ℝ)
          ((q (pptCoordinateEmbedding p q i)-1 : ℕ) : ℝ))
    (hsmall : ∀ i : Fin (pptUnequalCoordinates p q).card,
      S ≤ min ((p (pptCoordinateEmbedding p q i)-1 : ℕ) : ℝ)
        ((q (pptCoordinateEmbedding p q i)-1 : ℕ) : ℝ)) :
    ∀ i : Fin (pptUnequalCoordinates p q).card,
      |B (largestPrimeFactor (p (pptCoordinateEmbedding p q i)-1))/B z-
        B (largestPrimeFactor (q (pptCoordinateEmbedding p q i)-1))/B z| ≤
        (2*(i.val : ℝ)+1)*Real.sqrt (B S/B z)+Real.log (3*B z)/B z := by
  intro i
  have hanti := ppt_surviving_coordinates_strictAnti p q hpa hqa
  have hcancel := ppt_cancel_matching_coordinates p q (fun i => (hp i).1) heq
  exact ppt_normalized_coordinate_alignment
    (p ∘ pptCoordinateEmbedding p q) (q ∘ pptCoordinateEmbedding p q) i.isLt i.isLt
    hS hBS hB hSz hD hE (fun i => hp _) (fun i => hq _)
    hanti.1.antitone hanti.2.antitone hcancel (hp3 _) (hq3 _) (hpz _) (hqz _)
    (hDS i) (hES i) (hsmall i)

/-- The proved local normality height bound absorbs both terms of the
actual alignment estimate in the doubled paired-grid mesh. -/
theorem ppt_local_alignment_in_paired_mesh {A : ℝ} (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ∀ (h i : ℕ) (S u v : ℝ),
      (h : ℝ) ≤ A*Real.log t → 0 ≤ B S → B S ≤ (h : ℝ)^4 →
      |u-v| ≤ (2*(i : ℝ)+1)*Real.sqrt (B S/t)+Real.log (3*t)/t →
      |u-v| ≤ (2*(i : ℝ)+1)*(2*((Real.log t)^5/Real.sqrt t)) := by
  filter_upwards [ppt_local_normality_error_mesh hA, ppt_logarithmic_alignment_error,
    eventually_gt_atTop (1 : ℝ)] with t hmesh hlog ht
  intro h i S u v hdim hBS hheight halign
  have hsqrt := hmesh h S hdim hBS hheight
  have hmesh0 : 0 ≤ (Real.log t)^5/Real.sqrt t := by
    have hlog0 : 0 < Real.log t := Real.log_pos ht
    positivity
  have hcoef : 0 ≤ 2*(i : ℝ)+1 := by positivity
  have hh := mul_le_mul_of_nonneg_left hsqrt hcoef
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  nlinarith only [halign, hh, hlog, hmesh0, mul_nonneg hi hmesh0]

/-- The actual paired label supplies both errors used by the row
estimate, with one common bound.  These are conclusions about the grid,
not additional hypotheses on its rounded coordinates. -/
lemma ppt_paired_grid_row_errors {b : ℕ} {δ ζ θ : ℝ}
    (hδ : 0 < δ) (u v : Fin b → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (halign : ∀ i, |u i-v i| ≤ (2*(i.val : ℝ)+1)*δ) :
    let label := fun i => collisionGridIndex δ (u i) (v i)
    (∀ i : Fin b, 0 < i.val →
      pairedGridUpper δ ζ label i ≤ u i+(2*(b : ℝ)+3)*δ) ∧
    (∀ i ∈ Finset.Icc 1 (b-1),
      pairedGridUpper δ ζ label i-pptGridLower δ θ label i ≤ (2*(b : ℝ)+3)*δ) := by
  dsimp only
  constructor
  · intro i hi
    have hi' : i.val ∈ Finset.Icc 1 (b-1) :=
      Finset.mem_Icc.mpr ⟨hi, by have := i.isLt; omega⟩
    exact paired_grid_approximation hδ u v hu hv halign hi'
  · intro i hi
    rw [ppt_grid_width δ ζ θ _ hi]
    apply mul_le_mul_of_nonneg_right _ hδ.le
    have hib : i ≤ b := (Finset.mem_Icc.mp hi).2.trans (Nat.sub_le _ _)
    have hir : (i : ℝ) ≤ b := by exact_mod_cast hib
    linarith only [hir]

/-- Convert the concrete inverse-cube margin to the fixed
inverse-log-cube saving used by the comparison-block sum. -/
lemma ppt_residual_inverse_log_saving {A t : ℝ} {H r : ℕ}
    (_hA : 0 < A) (_ht : 0 < Real.log t)
    (hrH : r+1 ≤ H) (hdim : (H : ℝ) ≤ A*Real.log t) :
    1/(80*A^3)/(Real.log t)^3 ≤ rowContractionError r/16 := by
  have hr : (r+1 : ℝ) ≤ A*Real.log t := by
    have hh : (r+1 : ℝ) ≤ H := by exact_mod_cast hrH
    exact hh.trans hdim
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r+1) hr 3
  have hh : 1/(80*(A*Real.log t)^3) ≤ 1/(80*(r+1 : ℝ)^3) :=
    one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left hp (by norm_num))
  calc
    _ = 1/(80*(A*Real.log t)^3) := by rw [div_div, mul_pow]; ring
    _ ≤ 1/(80*(r+1 : ℝ)^3) := hh
    _ = rowContractionError r/16 := by unfold rowContractionError; rw [div_div]; ring

/-- On a late residual row, the actual candidate coordinates bound the
rounded largest-factor coordinates.  The fixed endpoint error and every
mesh contribution are absorbed uniformly in the logarithmic local length. -/
theorem ppt_local_residual_exponent {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n k H : ℕ) (budget c S e w δ : ℝ)
      (p q : Fin k → ℕ) (v : Fin n → ℝ)
      (ι : Fin (pptUnequalCoordinates p q).card ↪o Fin n)
      (ν μ : ℕ → ℝ),
      ∀ hk : 0 < k, ∀ hb : 0 < (pptUnequalCoordinates p q).card,
      v ∈ relaxedGeometricFamily m n budget c →
      p ⟨0,hk⟩ ≠ q ⟨0,hk⟩ → (∀ i, 3 ≤ p i) →
      (p ⟨0,hk⟩-1 : ℕ) ≤ z →
      (∀ i, v (ι i) = B (p (pptCoordinateEmbedding p q i))) →
      1 ≤ H → (pptUnequalCoordinates p q).card ≤ H →
      m-((ι ⟨0,hb⟩).val+1)+1 ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      0 ≤ δ → δ ≤ 2*((Real.log (B z))^5/Real.sqrt (B z)) →
      e ≤ (2*((pptUnequalCoordinates p q).card : ℝ)+4)*δ →
      w ≤ (4*((pptUnequalCoordinates p q).card : ℝ)+3)*δ →
      Real.sqrt (B S/B z) ≤ δ →
      (∀ i : Fin (pptUnequalCoordinates p q).card, 0 < i.val →
        ν i ≤ B (largestPrimeFactor (p (pptCoordinateEmbedding p q i)-1))/B z+e) →
      (∀ i ∈ Finset.Icc 1 ((pptUnequalCoordinates p q).card-1), ν i-μ i ≤ w) →
      -2+(∑ i ∈ Finset.Icc 1 ((pptUnequalCoordinates p q).card-1),
        a i*(B (comparisonCutoffs z ν i)/B z))+
        comparisonError (pptUnequalCoordinates p q).card z S
          (comparisonCutoffs z ν) (comparisonCutoffs z μ) ≤
        -1-rowContractionError (m-((ι ⟨0,hb⟩).val+1))/16 := by
  filter_upwards [B_tendsto.eventually (ppt_local_head_error_absorbed hA (by norm_num : (0 : ℝ) ≤ 1)),
    B_tendsto.eventually (ppt_grid_error_absorbed_two_mesh hA),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_ge_atTop (Real.exp 1)] with z hheaderr hgriderr hB hz
  intro m n k H budget c S e w δ p q v ι ν μ hk hb hv hfirst hp3 hpz hcoords
    hH hbH hrH hdim hδ hδmax he hw hη hν hwidth
  have hzero : pptCoordinateEmbedding p q ⟨0,hb⟩ = ⟨0,hk⟩ := by
    obtain ⟨hb', hh⟩ := ppt_coordinate_first_survives hk p q hfirst
    simpa only using hh
  have hhead : v (ι ⟨0,hb⟩) ≤ B z+1 := by
    rw [hcoords, hzero]
    exact prime_coordinate_endpoint_bound (hp3 _) hz hpz
  have hround (i : Fin (pptUnequalCoordinates p q).card) (hi : 0 < i.val) :
      ν i ≤ v (ι i)/B z+e := by
    have hp : 3 ≤ p (pptCoordinateEmbedding p q i) := hp3 _
    have hl : (1 : ℝ) < largestPrimeFactor (p (pptCoordinateEmbedding p q i)-1) := by
      exact_mod_cast one_lt_largestPrimeFactor
        (show 2 ≤ p (pptCoordinateEmbedding p q i)-1 by omega)
    have hnat : largestPrimeFactor (p (pptCoordinateEmbedding p q i)-1) ≤
        p (pptCoordinateEmbedding p q i) :=
      (largestPrimeFactor_le_self (by omega)).trans (Nat.sub_le _ _)
    have hmono : B (largestPrimeFactor (p (pptCoordinateEmbedding p q i)-1)) ≤
        B (p (pptCoordinateEmbedding p q i)) :=
      Real.log_le_log (Real.log_pos hl)
        (Real.log_le_log (zero_lt_one.trans hl) (Nat.cast_le.mpr hnat))
    have hh := div_le_div_of_nonneg_right hmono hB.le
    rw [← hcoords i] at hh
    apply (hν i hi).trans
    linarith only [hh]
  apply ppt_relaxed_surviving_exponent hv ι hb ν μ hB hB.ne' hhead
    (hheaderr H (m-((ι ⟨0,hb⟩).val+1)) hdim hrH) hround hwidth
  exact hgriderr (pptUnequalCoordinates p q).card H
    (m-((ι ⟨0,hb⟩).val+1)) e w (Real.sqrt (B S/B z)) δ
    hH hbH hrH hdim hδ hδmax he hw hη

end TotientAsymptotic

end

end OAI
