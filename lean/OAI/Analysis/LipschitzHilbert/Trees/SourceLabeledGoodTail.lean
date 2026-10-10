import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledGoodEvents
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledVariationTail

namespace OAI

/-! Assemble the original error, narrow main square and narrow centered
variation tails into the physical bad-reference event. Polynomial powers
and exponential losses are fixed before the family is selected. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem physicalAngularError_nonneg (P : SourceLabeledLattice N κ Label Item)
    (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    0 ≤ P.physicalAngularError t a b v g z := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro l _
  exact Finset.sum_nonneg (fun u _ =>
    mul_nonneg (norm_nonneg _) (tileEnvelope_nonneg _ _ _ _ _ _))

/-- The actual three-reference event has a uniform tail, provided the
three already proved component tails are supplied two rates stronger. -/
theorem eventually_physical_reference_good_tail (a q p J : ℝ) :
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
      (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (A y u W : ℝ), 0 < W →
      (volume.restrict (Ico u (u+W)))
        {x | L^(p+7) ≤ P.physicalAngularError t c b v g (x,y+t*x)} ≤
        ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal W →
      (volume.restrict (Ico u (u+W)))
        {x | L^(2*q+9) ≤ P.physicalMainSquare t c b v g y x} ≤
        ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal W →
      (volume.restrict (Ico u (u+W)))
        {x | L^(2*q+10) ≤ |P.physicalCenteredMaskedVariation alt hAlt t c b v g T L A y x|} ≤
        ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal W →
      (volume.restrict (Ico u (u+W)))
        {x | (x,y+t*x) ∈ P.physicalReferenceBad alt hAlt t c b v g T L A
          (p+7) (2*q+9) (max (2*q+10) (a+p+7)+1)} ≤
        ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal W := by
  filter_upwards [eventually_physicalReferenceBad_tail J,
    eventually_physical_full_variation_tail a (q+1) p (J+1),
    eventually_ge_atTop (0:ℝ)] with L hbad hfull hL
  intro N κ Label Item _ _ P horder hP alt hAlt t c b hb hb1 v hv g hg hg1 T
    A y u W hW hE hS hV
  have hweaken : ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal W ≤
      ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal W := by
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith
  have hEabs : (volume.restrict (Ico u (u+W)))
      {x | L^(p+7) ≤ |P.physicalAngularError t c b v g (x,y+t*x)|} ≤
        ENNReal.ofReal (Real.exp (-((J+1)+1)*L))*ENNReal.ofReal W := by
    simpa only [abs_of_nonneg (P.physicalAngularError_nonneg t c b v g _),
      show J+1+1 = J+2 by ring] using hE
  have hfull' := hfull N κ Label Item P horder hP alt hAlt t c b hb hb1 v hv g hg hg1
    T A y u W (by simpa only [show 2*(q+1)+8 = 2*q+10 by ring,
      show J+1+1 = J+2 by ring] using hV) hEabs
  have hV' : (volume.restrict (Ico u (u+W)))
      {x | L^(max (2*q+10) (a+p+7)+1) ≤ P.physicalMaskedVariation alt hAlt t b v g T L A y x} ≤
        ENNReal.ofReal (Real.exp (-(J+1)*L))*ENNReal.ofReal W := by
    apply (measure_mono (show
      {x | L^(max (2*q+10) (a+p+7)+1) ≤ P.physicalMaskedVariation alt hAlt t b v g T L A y x} ⊆
      {x | L^(max (2*q+10) (a+p+7)+1) ≤ |P.physicalMaskedVariation alt hAlt t b v g T L A y x|}
      from by
        intro x hx
        change L^(max (2*q+10) (a+p+7)+1) ≤
          P.physicalMaskedVariation alt hAlt t b v g T L A y x at hx
        change L^(max (2*q+10) (a+p+7)+1) ≤
          |P.physicalMaskedVariation alt hAlt t b v g T L A y x|
        exact hx.trans (le_abs_self _))).trans
    simpa only [show 2*(q+1)+8 = 2*q+10 by ring] using hfull'
  exact hbad N κ Label Item P alt hAlt t c b v g T A (p+7) (2*q+9)
    (max (2*q+10) (a+p+7)+1) y u W hW (hE.trans hweaken) (hS.trans hweaken) hV'

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
