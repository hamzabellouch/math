import OAI.GroupTheory.PolycyclicRecognition.Geometry.HarmonicAnalyticScales
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HarmonicDimensionCriterion
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HarmonicCoverFactorBound
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

/-! # A dimension bound independent of the chosen harmonic subspace -/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem uniform_harmonic_subspace_dimension_bound (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (V : Submodule ℝ (G → ℝ)) (basis : Module.Basis ι ℝ V) (d b : ℕ)
    (hk : 0 < Fintype.card ι)
    (hF : ∀ i, PolynomiallyBoundedOnWords S d (basis i).val)
    (hharm : ∀ f : V, CayleyHarmonic S f.val)
    (D : ℝ) (hD : 0 ≤ D)
    (hvol : ∀ R, ((wordBall S R).card : ℝ) ≤ D * (1 + (R : ℝ)) ^ b)
    (w : ℕ) (hw : 0 < w)
    (hwidth : 128 * (S.card : ℝ) * (harmonicScaleConstant b d) ^ 4 < (16 : ℝ) ^ (2 * w)) :
    Module.finrank ℝ V ≤ 2 * Nat.ceil (harmonicScaleConstant b d ^ w) := by
  let K := harmonicScaleConstant b d
  have hK : 1 < K := harmonicScaleConstant_gt_one b d
  have hK₀ : 0 < K := zero_lt_one.trans hK
  obtain ⟨a, i, j, hai, hij, hpos, hsmallVol, hcrossVol, hdet⟩ :=
    exists_harmonic_analytic_scales S hS hgen V basis d b hk hF D hD hvol w hw
  let r := harmonicRadius a i
  let R := harmonicRadius a j
  let R' := harmonicRadius a (j + 1)
  have hij' : i < j := by omega
  have haj : a ≤ j := by omega
  have hrR : 2 * r ≤ R := harmonicRadius_double_le hai hij'
  have hRnext : 8 * R ≤ R' := harmonicRadius_next_ge_eight haj
  have hrnext : 8 * r ≤ harmonicRadius a (i + 1) := harmonicRadius_next_ge_eight hai
  have hRpos : 0 < R := by dsimp [R, harmonicRadius]; positivity
  have h₁ : ((wordBall S (4 * r)).card : ℝ) ≤ K * (wordBall S (2 * r)).card := by
    calc
      _ ≤ ((wordBall S (harmonicRadius a (i + 1))).card : ℝ) := by
        exact_mod_cast card_le_card (wordBall_mono S (by omega : 4 * r ≤ harmonicRadius a (i + 1)))
      _ ≤ K * (wordBall S r).card := hsmallVol
      _ ≤ K * (wordBall S (2 * r)).card := mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (card_le_card (wordBall_mono S (by omega)))) hK₀.le
  have h₂ : ((wordBall S (7 * r)).card : ℝ) ≤ K * (wordBall S r).card := by
    exact (Nat.cast_le.mpr (card_le_card (wordBall_mono S
      (by omega : 7 * r ≤ harmonicRadius a (i + 1))))).trans hsmallVol
  have hsep : 32 * (S.card : ℝ) * K ^ 4 * (r : ℝ) ^ 2 < (R : ℝ) ^ 2 := by
    apply harmonicRadius_quadratic_separation (a := a) (i := i) (j := j) (w := w)
      hai (by omega) _ (by positivity)
    convert hwidth using 1
    ring
  have hfactor : harmonicCoverFactor S r R (2 * r) * K ^ 2 < 1 :=
    harmonic_cover_factor_small S r R hRpos K hK₀.le h₁ h₂ hsep
  obtain ⟨C, hC, hdis, hcover⟩ := exists_disjoint_wordBall_cover S hS (wordBall S R) r
  have hdim : Module.finrank ℝ V ≤ 2 * C.card :=
    harmonic_dimension_bound_from_gram S hS hgen V basis hharm C r R (2 * r) R'
      (by omega) (by omega) hdis hC hcover hpos K hK hdet hfactor
  have hpacking : C.card * (wordBall S r).card ≤ (wordBall S (R + r)).card := by
    apply disjoint_wordBall_packing_bound S C hdis 1 R
    intro x hx
    simpa only [mem_translatedWordBall, inv_one, one_mul] using hC hx
  have hball : ((wordBall S (R + r)).card : ℝ) ≤ K ^ w * (wordBall S r).card := by
    exact (Nat.cast_le.mpr (card_le_card (wordBall_mono S (by omega : R + r ≤ R')))).trans hcrossVol
  have hcpos : (0 : ℝ) < (wordBall S r).card :=
    Nat.cast_pos.mpr (card_pos.mpr ⟨1, one_mem_wordBall S r⟩)
  have hCreal : (C.card : ℝ) ≤ K ^ w := by
    apply (mul_le_mul_iff_left₀ hcpos).mp
    exact (by exact_mod_cast hpacking : (C.card : ℝ) * (wordBall S r).card ≤
      (wordBall S (R + r)).card).trans hball
  have hCN : C.card ≤ Nat.ceil (K ^ w) := by
    exact_mod_cast hCreal.trans (Nat.le_ceil (K ^ w))
  exact hdim.trans (Nat.mul_le_mul_left 2 hCN)

end PolycyclicRecognition

end

end OAI
