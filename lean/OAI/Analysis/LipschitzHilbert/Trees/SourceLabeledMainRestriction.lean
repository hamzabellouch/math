import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledMainTail
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceMainRestriction

namespace OAI

/-! Only nonzero frozen selectors enter the positive main scale.
Restricting to their fixed narrow reference cone is exact, and changes
the carrier bound without changing any retained physical packet or
positive envelope. The wide error family is not used in the main tail. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalFrozenCenteredCoefficient_eq_zero (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) (hz : ∀ k, b j l k t = 0) :
    P.physicalFrozenCenteredCoefficient t a b v g j l u = 0 := by
  ext k
  simp only [physicalFrozenCenteredCoefficient,analyzingCoefficient,WithLp.ofLp_toLp,
    hz k,zero_mul,ite_self,map_zero,mul_zero,integral_zero,PiLp.zero_apply]

variable (t R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => P.referenceFamily t t R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel t t R cone w

/-- The retained main family pays only the narrow cone's carrier
bound. Its absolute envelope constant is unchanged. -/
theorem referenceSelf_constant :
    (Q).constant = P.absoluteConstant*(F*cone+2) := by
  unfold constant absoluteConstant referenceFamily
  ring

theorem referenceSelf_absoluteConstant : (Q).absoluteConstant = P.absoluteConstant := rfl

theorem referenceSelf_snappedSite (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).snappedSite j l u = P.snappedSite j (orig j l) u := by
  change snappedLatticeSite (P.originX j (orig j l))
    (P.originZ j (orig j l)+(t-t)*P.originX j (orig j l)) (P.length j) P.width
    (P.rowSlope j (orig j l)+(t-t)) (P.site j (orig j l) u) = _
  simp only [sub_self,zero_mul,add_zero]
  rfl

theorem referenceSelf_positiveEnvelope (j : Fin N) (l : (Q).labels j)
    (u : Item j l) (y x : ℝ) :
    (Q).positiveEnvelope j l u y x = P.positiveEnvelope j (orig j l) u y x := by
  unfold positiveEnvelope
  rw [P.referenceSelf_snappedSite t R cone w F hw hcone hF hwide hfrequency]
  rfl

theorem referenceSelf_frozenCenteredCoefficient (a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalFrozenCenteredCoefficient t a (fun j l k s => b j (orig j l) k s)
      v g j l u = P.physicalFrozenCenteredCoefficient t a b v g j (orig j l) u := by
  ext k
  simp only [physicalFrozenCenteredCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g z k*starRingEnd ℂ
      (if |v z-t| ≤ a*(2:ℝ)^j.val then b j (orig j l) k t*(Q).physicalPacket t j l u k z else 0)
      ∂volume.prod volume) = _
  have hp (z : ℝ×ℝ) : (Q).physicalPacket t j l u k z =
      P.physicalPacket t j (orig j l) u k z := congrArg
        (fun f : SchwartzMap (ℝ×ℝ) ℂ => f z)
        (P.referenceFamily_physicalPacket t t R cone w F hw hcone hF hwide hfrequency j l u k)
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  exact congrArg (fun f : ℂ => g z k*starRingEnd ℂ
    (if |v z-t| ≤ a*(2:ℝ)^j.val then b j (orig j l) k t*f else 0)) (hp z)

/-- The positive main scale may be restricted to the narrow fixed
reference family before any probabilistic or variational estimate. -/
theorem physicalMainScale_eq_narrow_reference (a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hshort : ∀ j l k, b j l k t ≠ 0 → P.length j ≤ R)
    (hsupport : ∀ j l k, b j l k t ≠ 0 → |t+P.rowSlope j l-t| ≤ cone*w/P.length j)
    (j : Fin N) (y x : ℝ) :
    P.physicalMainScale t a b v g j y x =
      (Q).physicalMainScale t a (fun j l k s => b j (orig j l) k s) v g j y x := by
  let f (l : P.labels j) (u : Item j l) : ℝ :=
    ‖P.physicalFrozenCenteredCoefficient t a b v g j l u‖*P.positiveEnvelope j l u y x
  have hsum := P.sum_reference_frozen (E := ℝ) t t R cone w j
    (fun l _u k => b j l k t) f
    (fun l _u k hk => hshort j l k hk)
    (fun l _u k hk => hsupport j l k hk)
    (fun l u hz => by
      dsimp only [f]
      rw [P.physicalFrozenCenteredCoefficient_eq_zero t a b v g j l u hz,norm_zero,zero_mul])
  unfold physicalMainScale
  symm
  calc
    _ = ∑ l : P.referenceLabels t t R cone w j, ∑ u : Item j l, f (orig j l) u := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro u _
      rw [P.referenceSelf_frozenCenteredCoefficient t R cone w F hw hcone hF hwide hfrequency,
        P.referenceSelf_positiveEnvelope t R cone w F hw hcone hF hwide hfrequency]
    _ = _ := hsum

theorem physicalMainSquare_eq_narrow_reference (a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hshort : ∀ j l k, b j l k t ≠ 0 → P.length j ≤ R)
    (hsupport : ∀ j l k, b j l k t ≠ 0 → |t+P.rowSlope j l-t| ≤ cone*w/P.length j)
    (y x : ℝ) :
    P.physicalMainSquare t a b v g y x =
      (Q).physicalMainSquare t a (fun j l k s => b j (orig j l) k s) v g y x := by
  unfold physicalMainSquare
  simp_rw [P.physicalMainScale_eq_narrow_reference t R cone w F hw hcone hF hwide hfrequency
    a b v g hshort hsupport]

theorem referenceSelf_alt_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) (k : κ) :
    ((Q).withProfile (fun j l u k => alt j (orig j l) u k)
      (fun j l u k => hAlt j (orig j l) u k)).physicalPacket t j l u k =
      (P.withProfile alt hAlt).physicalPacket t j (orig j l) u k := by
  exact (P.withProfile alt hAlt).referenceFamily_physicalPacket
    t t R cone w F hw hcone hF hwide hfrequency j l u k

/-- The same exact narrow restriction holds for the masked main
synthesis, retaining the alternate profile and each original top mask. -/
theorem physicalCenteredMaskedBand_eq_narrow_reference
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)
    (hshort : ∀ j l k, b j l k t ≠ 0 → P.length j ≤ R)
    (hsupport : ∀ j l k, b j l k t ≠ 0 → |t+P.rowSlope j l-t| ≤ cone*w/P.length j)
    (j : Fin N) (x : ℝ) :
    P.physicalCenteredMaskedBand alt hAlt t a b v g T L A y j x =
      (Q).physicalCenteredMaskedBand (fun j l u k => alt j (orig j l) u k)
        (fun j l u k => hAlt j (orig j l) u k) t a
        (fun j l k s => b j (orig j l) k s) v g
        (fun j l u => T j (orig j l) u) L A y j x := by
  ext k
  let f (l : P.labels j) (u : Item j l) : ℂ :=
    P.physicalFrozenCenteredCoefficient t a b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x)
  have hsum := P.sum_reference_frozen (E := ℂ) t t R cone w j
    (fun l _u k => b j l k t) f
    (fun l _u k hk => hshort j l k hk)
    (fun l _u k hk => hsupport j l k hk)
    (fun l u hz => by
      have hc := congrArg (fun c : EuclideanSpace ℂ κ => c k)
        (P.physicalFrozenCenteredCoefficient_eq_zero t a b v g j l u hz)
      dsimp only [f]
      rw [hc]
      simp)
  simp only [physicalCenteredMaskedBand,WithLp.ofLp_toLp]
  symm
  calc
    _ = ∑ l : P.referenceLabels t t R cone w j, ∑ u : Item j l, f (orig j l) u := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro u _
      rw [P.referenceSelf_frozenCenteredCoefficient t R cone w F hw hcone hF hwide hfrequency,
        P.referenceSelf_alt_physicalPacket t R cone w F hw hcone hF hwide hfrequency]
    _ = _ := hsum

theorem physicalCenteredMaskedVariation_eq_narrow_reference
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y x : ℝ)
    (hshort : ∀ j l k, b j l k t ≠ 0 → P.length j ≤ R)
    (hsupport : ∀ j l k, b j l k t ≠ 0 → |t+P.rowSlope j l-t| ≤ cone*w/P.length j) :
    P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x =
      (Q).physicalCenteredMaskedVariation (fun j l u k => alt j (orig j l) u k)
        (fun j l u k => hAlt j (orig j l) u k) t a
        (fun j l k s => b j (orig j l) k s) v g
        (fun j l u => T j (orig j l) u) L A y x := by
  unfold physicalCenteredMaskedVariation
  congr 2
  funext j
  exact P.physicalCenteredMaskedBand_eq_narrow_reference
    t R cone w F hw hcone hF hwide hfrequency alt hAlt a b v g T L A y hshort hsupport j x

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
