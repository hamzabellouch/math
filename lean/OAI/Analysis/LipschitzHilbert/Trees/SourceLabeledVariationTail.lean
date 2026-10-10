import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledVariationSplit
import OAI.Analysis.LipschitzHilbert.Trees.SourceBadEventUnion

namespace OAI

/-! Combining the actual narrow main-variation tail with the positive
angular-error tail costs a single extra polynomial power. The cutoff
exponent is fixed independently of the mass stopping threshold. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert

theorem variation_two_term_bad_subset {X : Type*} (F U E : X → ℝ)
    {L A a r s : ℝ} (hL : 2 ≤ L) (_hA : 0 ≤ A) (hAb : A ≤ L^a)
    (hF : ∀ x, |F x| ≤ |U x|+A*|E x|) :
    {x | L^(max r (a+s)+1) ≤ |F x|} ⊆
      {x | L^r ≤ |U x|} ∪ {x | L^s ≤ |E x|} := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  intro x hx
  by_contra hn
  have hU : |U x| < L^r := by
    by_contra h
    exact hn (Or.inl (not_lt.mp h))
  have hE : |E x| < L^s := by
    by_contra h
    exact hn (Or.inr (not_lt.mp h))
  have hAE : A*|E x| ≤ L^(a+s) := by
    calc
      _ ≤ L^a*L^s := mul_le_mul hAb hE.le (abs_nonneg _) (Real.rpow_nonneg hL0.le _)
      _ = _ := (Real.rpow_add hL0 _ _).symm
  have hsmall : |F x| < L^r+L^(a+s) :=
    (hF x).trans_lt (add_lt_add_of_lt_of_le hU hAE)
  have hbig : L^r+L^(a+s) ≤ L^(max r (a+s)+1) := by
    calc
      _ ≤ L^(max r (a+s))+L^(max r (a+s)) := add_le_add
        (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
        (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _))
      _ = 2*L^(max r (a+s)) := by ring
      _ ≤ L*L^(max r (a+s)) := mul_le_mul_of_nonneg_right hL (by positivity)
      _ = _ := by rw [Real.rpow_add hL0,Real.rpow_one]; ring
  exact (not_le_of_gt (hsmall.trans_le hbig)) hx

theorem eventually_variation_two_term_tail (a r s J : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X)
      (F U E : X → ℝ) (A : ℝ) (mass : ℝ≥0∞),
      0 ≤ A → A ≤ L^a → (∀ x, |F x| ≤ |U x|+A*|E x|) →
      μ {x | L^r ≤ |U x|} ≤ ENNReal.ofReal (Real.exp (-(J+1)*L))*mass →
      μ {x | L^s ≤ |E x|} ≤ ENNReal.ofReal (Real.exp (-(J+1)*L))*mass →
      μ {x | L^(max r (a+s)+1) ≤ |F x|} ≤
        ENNReal.ofReal (Real.exp (-J*L))*mass := by
  filter_upwards [eventually_ge_atTop (2:ℝ),
    eventually_source_polynomial_exp 2 0 J (by norm_num)] with L hL hdecay
  simp only [Real.rpow_zero,mul_one] at hdecay
  intro X _ μ F U E A mass hA hAb hF hU hE
  apply (measure_mono (variation_two_term_bad_subset F U E hL hA hAb hF)).trans
  apply (measure_union_le _ _).trans
  apply (add_le_add hU hE).trans
  calc
    _ = ENNReal.ofReal (2*Real.exp (-(J+1)*L))*mass := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hdecay) le_rfl

namespace SourceLabeledLattice

/-- The two separate tails control the full original masked synthesis,
using the previously proved exact main/error decomposition. -/
theorem eventually_physical_full_variation_tail (a q p J : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order → P.absoluteConstant ≤ L^a →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t c : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (_hb : ∀ j l k, Measurable (b j l k)) (_hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1)
      (T : ∀ j (l : P.labels j), Item j l → SlopeBox)
      (maskExponent y u H : ℝ),
      (volume.restrict (Ico u (u+H)))
        {x | L^(2*q+8) ≤ |P.physicalCenteredMaskedVariation
          alt hAlt t c b v g T L maskExponent y x|} ≤
        ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal H →
      (volume.restrict (Ico u (u+H)))
        {x | L^(p+7) ≤ |P.physicalAngularError t c b v g (x,y+t*x)|} ≤
        ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal H →
      (volume.restrict (Ico u (u+H)))
        {x | L^(max (2*q+8) (a+p+7)+1) ≤ |P.physicalMaskedVariation
          alt hAlt t b v g T L maskExponent y x|} ≤
        ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  filter_upwards [eventually_variation_two_term_tail a (2*q+8) (p+7) J] with L hL
  intro N κ Label Item _ _ P horder hP alt hAlt t c b hb hb1 v hv g hg hg1 T
    maskExponent y u H hmain herror
  have hbound (x : ℝ) : |P.physicalMaskedVariation alt hAlt t b v g T L maskExponent y x| ≤
      |P.physicalCenteredMaskedVariation alt hAlt t c b v g T L maskExponent y x|+
        P.absoluteConstant*|P.physicalAngularError t c b v g (x,y+t*x)| := by
    rw [abs_of_nonneg (show 0 ≤ P.physicalMaskedVariation
      alt hAlt t b v g T L maskExponent y x from cubicVariation_nonneg _ _),
      abs_of_nonneg (show 0 ≤ P.physicalCenteredMaskedVariation
        alt hAlt t c b v g T L maskExponent y x from cubicVariation_nonneg _ _)]
    apply (P.physicalMaskedVariation_le_main_add_error
      alt hAlt t c b v g T L maskExponent y horder hb hb1 hv hg hg1 x).trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_abs_self _) P.absoluteConstant_pos.le)
  have h := hL ℝ (volume.restrict (Ico u (u+H))) _ _ _ P.absoluteConstant
    (ENNReal.ofReal H) P.absoluteConstant_pos.le hP hbound hmain herror
  simpa only [show a+(p+7) = a+p+7 by ring] using h

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
