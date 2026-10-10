import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledActiveReference
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedConcentration
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationSplit

namespace OAI

/-! Only frozen-active labels enter the centered main term. Their actual
angular separation bounds the modulation parameter, independently of
the wide cone used for the positive angular error. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)

theorem frozenActive_carrier_bound (w F Cb : ℝ) (hw : 0 < w)
    (hF : 0 ≤ F) (_hCb : 0 ≤ Cb) (hfreq : ∀ k, |P.frequency k| ≤ F/w)
    (hangle : ∀ j l, (∃ k, b j l k t ≠ 0) → |P.rowSlope j l| ≤ Cb*w/P.length j)
    (j : Fin N) (l : P.frozenActiveLabels t b j) (k : κ) :
    |P.frequency k*P.rowSlope j (P.frozenActiveOriginalLabel t b j l)*P.length j| ≤ F*Cb := by
  have hs := hangle j _ (P.frozenActiveLabel_nonzero t b j l)
  rw [abs_mul,abs_mul,abs_of_pos (P.length_pos j)]
  calc
    _ ≤ (F/w)*(Cb*w/P.length j)*P.length j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (hfreq k) hs (abs_nonneg _) (div_nonneg hF hw.le)) (P.length_pos j).le
    _ = F*Cb := by field_simp [hw.ne',(P.length_pos j).ne']

/-- Changing a bound field changes no packet; the centered family uses
the narrow modulation bound supplied by active labels. -/
def activeMainFamily (w F Cb : ℝ) (hw : 0 < w) (hF : 0 ≤ F) (hCb : 0 ≤ Cb)
    (hfreq : ∀ k, |P.frequency k| ≤ F/w)
    (hangle : ∀ j l, (∃ k, b j l k t ≠ 0) → |P.rowSlope j l| ≤ Cb*w/P.length j) :
    SourceLabeledLattice N κ Label Item :=
  { P.frozenActiveFamily t b with
    carrierBound := F*Cb
    carrierBound_nonneg := mul_nonneg hF hCb
    carrier_bound := P.frozenActive_carrier_bound t b w F Cb hw hF hCb hfreq hangle }

variable (w F Cb : ℝ) (hw : 0 < w) (hF : 0 ≤ F) (hCb : 0 ≤ Cb)
  (hfreq : ∀ k, |P.frequency k| ≤ F/w)
  (hangle : ∀ j l, (∃ k, b j l k t ≠ 0) → |P.rowSlope j l| ≤ Cb*w/P.length j)
local notation "Q" => P.activeMainFamily t b w F Cb hw hF hCb hfreq hangle

theorem activeMainFamily_constant : (Q).constant = P.absoluteConstant*(F*Cb+2) := by
  unfold constant absoluteConstant activeMainFamily frozenActiveFamily
  ring

theorem activeMainFamily_topGeometry {T : SlopeBox} {K : ℝ} {D : ℕ}
    (G : SourceLabeledTopGeometry P T K D) : SourceLabeledTopGeometry Q T K D where
  length_le := G.length_le
  width_le := G.width_le
  centerX_le := fun j l u => G.centerX_le j (P.frozenActiveOriginalLabel t b j l) u
  centerZ_le := fun j l u => G.centerZ_le j (P.frozenActiveOriginalLabel t b j l) u
  order_le := G.order_le
  scale_eq := G.scale_eq

theorem activeMainFamily_rawInterval
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (a : ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    ((Q).withProfile
        (fun j l => alt j (P.frozenActiveOriginalLabel t b j l))
        (fun j l => hAlt j (P.frozenActiveOriginalLabel t b j l))).rawInterval
      ((Q).physicalFrozenCenteredCoefficient t a (P.frozenActiveSelector t b) v g)
      i lower upper x y =
    (P.withProfile alt hAlt).rawInterval (P.physicalFrozenCenteredCoefficient t a b v g)
      i lower upper x y := by
  rw [rawInterval_eq_band_sum _ _ _ _ _ hlu,rawInterval_eq_band_sum _ _ _ _ _ hlu]
  apply Finset.sum_congr rfl
  intro j _
  ext k
  simp only [rawBand,vectorPacketSynthesis,packetSynthesis_apply,WithLp.ofLp_toLp,
    Fintype.sum_sigma]
  exact P.sum_frozenActive_of_zero t b j
    (fun l u => P.physicalFrozenCenteredCoefficient t a b v g j l u k*
      (P.withProfile alt hAlt).raw i j l u k y x)
    (fun l hz u => by
      have hzero := congrArg (fun c : EuclideanSpace ℂ κ => c k)
        (P.physicalFrozenCenteredCoefficient_eq_zero t a b v g j l u hz)
      rw [hzero]
      simp)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
