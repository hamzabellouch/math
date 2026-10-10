import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationSplit

namespace OAI

/-! Exact linearity of the covariant signal and the joint triangle
bound for the original selector coefficient split. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
  (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

include hb hb1 hv hg hg1

theorem selector_covariantInterval_split (hscale : P.scale ≠ 0)
    (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    covariantSignal P.frequency
      (fun k yy => (P.withProfile alt hAlt).rawInterval
        (P.physicalMultiplierCoefficient t b v g) 0 lower upper x yy k) y =
    covariantSignal P.frequency
      (fun k yy => (P.withProfile alt hAlt).rawInterval
        (P.physicalFrozenCenteredCoefficient t a b v g) 0 lower upper x yy k) y+
    covariantSignal P.frequency
      (fun k yy => (P.withProfile alt hAlt).rawInterval
        (P.physicalAngularErrorCoefficient t a b v g) 0 lower upper x yy k) y := by
  let Q := P.withProfile alt hAlt
  apply (smul_right_injective (M := EuclideanSpace ℂ κ) (by exact hscale : Q.scale ≠ 0))
  change Q.scale • _ = Q.scale • _
  rw [smul_add,Q.rawInterval_scaled_covariant,Q.rawInterval_scaled_covariant,
    Q.rawInterval_scaled_covariant]
  exact P.selector_rawInterval_split alt hAlt t a b v g hb hb1 hv hg hg1
    1 lower upper hlu x y

theorem selector_jointInterval_le (hscale : P.scale ≠ 0)
    (lower upper : ℕ) (hlu : lower ≤ upper) (W : ℝ) (hW : 0 ≤ W) (x y : ℝ) :
    ‖(P.withProfile alt hAlt).rawInterval (P.physicalMultiplierCoefficient t b v g)
      0 lower upper x y‖+W*‖covariantSignal P.frequency
        (fun k yy => (P.withProfile alt hAlt).rawInterval
          (P.physicalMultiplierCoefficient t b v g) 0 lower upper x yy k) y‖ ≤
    (‖(P.withProfile alt hAlt).rawInterval (P.physicalFrozenCenteredCoefficient t a b v g)
      0 lower upper x y‖+W*‖covariantSignal P.frequency
        (fun k yy => (P.withProfile alt hAlt).rawInterval
          (P.physicalFrozenCenteredCoefficient t a b v g) 0 lower upper x yy k) y‖)+
    (‖(P.withProfile alt hAlt).rawInterval (P.physicalAngularErrorCoefficient t a b v g)
      0 lower upper x y‖+W*‖covariantSignal P.frequency
        (fun k yy => (P.withProfile alt hAlt).rawInterval
          (P.physicalAngularErrorCoefficient t a b v g) 0 lower upper x yy k) y‖) := by
  rw [P.selector_rawInterval_split alt hAlt t a b v g hb hb1 hv hg hg1 0 lower upper hlu,
    P.selector_covariantInterval_split alt hAlt t a b hb hb1 v hv g hg hg1 hscale
      lower upper hlu x y]
  have hval := norm_add_le
    ((P.withProfile alt hAlt).rawInterval (P.physicalFrozenCenteredCoefficient t a b v g)
      0 lower upper x y)
    ((P.withProfile alt hAlt).rawInterval (P.physicalAngularErrorCoefficient t a b v g)
      0 lower upper x y)
  have hcov := mul_le_mul_of_nonneg_left (norm_add_le
    (covariantSignal P.frequency (fun k yy => (P.withProfile alt hAlt).rawInterval
      (P.physicalFrozenCenteredCoefficient t a b v g) 0 lower upper x yy k) y)
    (covariantSignal P.frequency (fun k yy => (P.withProfile alt hAlt).rawInterval
      (P.physicalAngularErrorCoefficient t a b v g) 0 lower upper x yy k) y)) hW
  linarith

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
