import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedTopPhysical
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedTopReference
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedConcentration
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceSelectorGeometry

namespace OAI

/-! The assigned-top constructor preserves the original selectors,
packet spectra, and local label count. Its geometry is supplied by the
actual selected packets; the global longest-scale bound remains explicit. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)

theorem assignedTopLabel_first (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j) : l.val.1 = top :=
  Finset.mem_singleton.mp (Finset.mem_product.mp l.property).1

def assignedTopLabel (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j) : P.labels j := l.val.2

theorem assignedTopLabel_injective (j : Fin N) :
    Function.Injective (P.assignedTopLabel packets assigned top j) := by
  intro l m h
  apply Subtype.ext
  exact Prod.ext ((P.assignedTopLabel_first packets assigned top j l).trans
    (P.assignedTopLabel_first packets assigned top j m).symm) h

theorem assignedTopItem_mem (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (⟨j,⟨l.val.2,u.val⟩⟩ : P.PacketIndex) ∈ packets := u.property.1

theorem assignedTopItem_assignment (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    assigned ⟨j,⟨l.val.2,u.val⟩⟩ = top :=
  u.property.2.trans (P.assignedTopLabel_first packets assigned top j l)

theorem assignedTopFamily_absoluteConstant :
    (P.assignedTopFamily packets assigned top).absoluteConstant = P.absoluteConstant := rfl

theorem assignedTopFamily_raw (i : Fin 3) (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) (k : κ) (y : ℝ) :
    (P.assignedTopFamily packets assigned top).raw i j l u k y =
      P.raw i j l.val.2 u.val k y := rfl

def assignedTopSelector (b : ∀ j, P.labels j → κ → ℝ → ℂ) :
    ∀ j, (P.assignedTopFamily packets assigned top).labels j → κ → ℝ → ℂ :=
  fun j l => b j l.val.2

theorem assignedTopFamily_localMultiplicity (t d : ℝ) (M : ℕ) (j : Fin N)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d M) :
    SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : (P.assignedTopFamily packets assigned top).labels j =>
        t+(P.assignedTopFamily packets assigned top).rowSlope j l) d M := by
  intro a
  apply (Finset.card_le_card_of_injOn (P.assignedTopLabel packets assigned top j) ?_ ?_).trans (hlocal a)
  · intro l hl
    obtain ⟨_,hlo,hhi⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlo,hhi⟩
  · intro l _ m _ h
    exact P.assignedTopLabel_injective packets assigned top j h

theorem assignedTopFamily_topGeometry (T : SlopeBox) (K : ℝ) (D : ℕ)
    (hlength : P.topLength ≤ K*T.length) (hwidth : P.width ≤ K*T.width)
    (horder : 3+2*(8*D+1) ≤ P.order) (hscale : P.scale = 4*(K*T.width))
    (hX : ∀ q ∈ packets, assigned q = top →
      |P.actualX q.1 q.2.1 q.2.2-T.x|+P.length q.1 ≤ K*T.length)
    (hZ : ∀ q ∈ packets, assigned q = top →
      |P.actualZ q.1 q.2.1 q.2.2-(T.y-T.slope*T.x)|+P.width ≤ K*T.width) :
    SourceLabeledTopGeometry (P.assignedTopFamily packets assigned top) T K D where
  length_le := hlength
  width_le := hwidth
  order_le := horder
  scale_eq := hscale
  centerX_le := fun j l u => hX ⟨j,⟨l.val.2,u.val⟩⟩
    (P.assignedTopItem_mem packets assigned top j l u)
    (P.assignedTopItem_assignment packets assigned top j l u)
  centerZ_le := fun j l u => hZ ⟨j,⟨l.val.2,u.val⟩⟩
    (P.assignedTopItem_mem packets assigned top j l u)
    (P.assignedTopItem_assignment packets assigned top j l u)

theorem assignedTopFamily_spectrum (t w cStar cEta CEta : ℝ)
    (hspectrum : ∀ q ∈ packets, assigned q = top → ∀ k xi eta,
      planarAngularFourier (P.physicalPacket t q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
      |xi+(t+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta) :
    ∀ j l u k xi eta,
      planarAngularFourier ((P.assignedTopFamily packets assigned top).physicalPacket
        t j l u k) (xi,eta) ≠ 0 →
      |xi+(t+(P.assignedTopFamily packets assigned top).rowSlope j l)*eta| ≤
        cStar/(P.assignedTopFamily packets assigned top).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
  intro j l u k xi eta hn
  exact hspectrum ⟨j,⟨l.val.2,u.val⟩⟩
    (P.assignedTopItem_mem packets assigned top j l u)
    (P.assignedTopItem_assignment packets assigned top j l u) k xi eta hn

theorem assignedTopFamily_alt_spectrum
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t w cStar cEta CEta : ℝ)
    (hspectrum : ∀ q ∈ packets, assigned q = top → ∀ k xi eta,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
      |xi+(t+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta) :
    ∀ j l u k xi eta,
      planarAngularFourier (((P.assignedTopFamily packets assigned top).withProfile
        (P.assignedTopAlternate packets assigned alt top)
        (P.assignedTopAlternate_bound packets assigned alt hAlt top)).physicalPacket
          t j l u k) (xi,eta) ≠ 0 →
      |xi+(t+(P.assignedTopFamily packets assigned top).rowSlope j l)*eta| ≤
        cStar/(P.assignedTopFamily packets assigned top).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
  intro j l u k xi eta hn
  exact hspectrum ⟨j,⟨l.val.2,u.val⟩⟩
    (P.assignedTopItem_mem packets assigned top j l u)
    (P.assignedTopItem_assignment packets assigned top j l u) k xi eta hn

theorem assignedTopFamily_active_separation (t w cb Cb : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hsep : ∀ j l, (∃ k, b j l k t ≠ 0) →
      cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) :
    ∀ j l, (∃ k, P.assignedTopSelector packets assigned top b j l k t ≠ 0) →
      cb*w/(P.assignedTopFamily packets assigned top).length j ≤
          |(P.assignedTopFamily packets assigned top).rowSlope j l| ∧
        |(P.assignedTopFamily packets assigned top).rowSlope j l| ≤
          Cb*w/(P.assignedTopFamily packets assigned top).length j := by
  intro j l hl
  exact hsep j l.val.2 hl

/-- The center estimate is expressed in the new top's physical shear
coordinates. Restricting to the reference cone does not enlarge it. -/
theorem assignedTopReference_topGeometry
    (oldSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (T : SlopeBox) (K : ℝ) (D : ℕ)
    (hlength : P.topLength ≤ K*T.length) (hwidth : P.width ≤ K*T.width)
    (horder : 3+2*(8*D+1) ≤ P.order) (hscale : P.scale = 4*(K*T.width))
    (hX : ∀ q ∈ packets, assigned q = top →
      |P.actualX q.1 q.2.1 q.2.2-T.x|+P.length q.1 ≤ K*T.length)
    (hZ : ∀ q ∈ packets, assigned q = top →
      |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-T.slope)*P.actualX q.1 q.2.1 q.2.2-
        (T.y-T.slope*T.x)|+P.width ≤ K*T.width) :
    SourceLabeledTopGeometry
      ((P.assignedTopFamily packets assigned top).referenceFamily oldSlope T.slope R cone w F
        hw hcone hF hwide hfrequency) T K D := by
  let A := P.assignedTopFamily packets assigned top
  refine ⟨hlength,hwidth,?_,?_,horder,hscale⟩
  · intro j l u
    let l' := A.referenceOriginalLabel oldSlope T.slope R cone w j l
    exact hX ⟨j,⟨l'.val.2,u.val⟩⟩
      (P.assignedTopItem_mem packets assigned top j l' u)
      (P.assignedTopItem_assignment packets assigned top j l' u)
  · intro j l u
    let l' := A.referenceOriginalLabel oldSlope T.slope R cone w j l
    have hz := A.referenceFamily_actualZ oldSlope T.slope R cone w F
      hw hcone hF hwide hfrequency j l u
    have he := congrArg (fun z : ℝ => |z-(T.y-T.slope*T.x)|+P.width) hz
    exact he.le.trans (hZ ⟨j,⟨l'.val.2,u.val⟩⟩
      (P.assignedTopItem_mem packets assigned top j l' u)
      (P.assignedTopItem_assignment packets assigned top j l' u))


section Reference
variable (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
  (hF : 0 ≤ F) (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top) oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top) oldSlope newSlope R cone w

/-- The reference label still points to its unique original label. -/
def assignedTopReferenceLabel (j : Fin N) (l : (Q).labels j) : P.labels j :=
  (orig j l).val.2

theorem assignedTopReference_condition (j : Fin N) (l : (Q).labels j) :
    P.referenceCondition oldSlope newSlope R cone w j (orig j l).val.2 :=
  ((P.assignedTopFamily packets assigned top).referenceLabelsEquiv oldSlope newSlope R cone w j l).property

theorem assignedTopReference_absoluteConstant : (Q).absoluteConstant = P.absoluteConstant := rfl

theorem assignedTopReference_physical_center (j : Fin N) (l : (Q).labels j) :
    newSlope+(Q).rowSlope j l = oldSlope+P.rowSlope j (orig j l).val.2 :=
  (P.assignedTopFamily packets assigned top).referenceFamily_physical_center oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l

theorem assignedTopReference_localMultiplicity (j : Fin N) (d : ℝ) (M : ℕ)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) d M) :
    SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : (Q).labels j => newSlope+(Q).rowSlope j l) d M :=
  (P.assignedTopFamily packets assigned top).referenceFamily_localMultiplicity oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j d M
      (P.assignedTopFamily_localMultiplicity packets assigned top oldSlope d M j hlocal)

theorem assignedTopReference_selector_support
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (radius d : Fin N → ℝ)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ radius j*d j) :
    ∀ j (l : (Q).labels j) k s, b j (orig j l).val.2 k s ≠ 0 →
      |s-(newSlope+(Q).rowSlope j l)| ≤ radius j*d j := by
  intro j l k s hb
  rw [P.assignedTopReference_physical_center packets assigned top oldSlope newSlope
    R cone w F hw hcone hF hwide hfrequency j l]
  exact hsupport j (orig j l).val.2 k s hb

theorem assignedTopReference_spectrum (cStar cEta CEta : ℝ)
    (hspectrum : ∀ q ∈ packets, assigned q = top → ∀ k xi eta,
      planarAngularFourier (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
      |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta) :
    ∀ j l u k xi eta,
      planarAngularFourier ((Q).physicalPacket newSlope j l u k) (xi,eta) ≠ 0 →
      |xi+(newSlope+(Q).rowSlope j l)*eta| ≤ cStar/(Q).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta :=
  (P.assignedTopFamily packets assigned top).referenceFamily_spectrum oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    cStar cEta CEta
    (P.assignedTopFamily_spectrum packets assigned top oldSlope w cStar cEta CEta hspectrum)

theorem assignedTopReference_alt_spectrum
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (cStar cEta CEta : ℝ)
    (hspectrum : ∀ q ∈ packets, assigned q = top → ∀ k xi eta,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
        oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
      |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta) :
    ∀ j l u k xi eta,
      planarAngularFourier (((Q).withProfile
        (fun j l u k => alt j (orig j l).val.2 u.val k)
        (fun j l u k => hAlt j (orig j l).val.2 u.val k)).physicalPacket
          newSlope j l u k) (xi,eta) ≠ 0 →
      |xi+(newSlope+(Q).rowSlope j l)*eta| ≤ cStar/(Q).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
  intro j l u k xi eta hn
  have hp := (P.assignedTopFamily packets assigned top).referenceFamily_alternate_physicalPacket
    oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    (P.assignedTopAlternate packets assigned alt top)
    (P.assignedTopAlternate_bound packets assigned alt hAlt top) j l u k
  have hn' : planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
      oldSlope j (orig j l).val.2 u.val k) (xi,eta) ≠ 0 := by
    intro hz
    apply hn
    exact (congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => planarAngularFourier f (xi,eta)) hp).trans hz
  have hs := hspectrum ⟨j,⟨(orig j l).val.2,u.val⟩⟩
    (P.assignedTopItem_mem packets assigned top j (orig j l) u)
    (P.assignedTopItem_assignment packets assigned top j (orig j l) u) k xi eta hn'
  have hc := P.assignedTopReference_physical_center packets assigned top oldSlope newSlope
    R cone w F hw hcone hF hwide hfrequency j l
  refine ⟨?_,hs.2⟩
  exact (congrArg (fun r : ℝ => |xi+r*eta|) hc).le.trans hs.1

theorem assignedTopReference_active_separation (cb Cb : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hsep : ∀ j l, (∃ k, b j l k newSlope ≠ 0) →
      cb*w/P.length j ≤ |oldSlope+P.rowSlope j l-newSlope| ∧
        |oldSlope+P.rowSlope j l-newSlope| ≤ Cb*w/P.length j) :
    ∀ j (l : (Q).labels j), (∃ k, b j (orig j l).val.2 k newSlope ≠ 0) →
      cb*w/(Q).length j ≤ |(Q).rowSlope j l| ∧
        |(Q).rowSlope j l| ≤ Cb*w/(Q).length j := by
  intro j l h
  have hs := hsep j (orig j l).val.2 h
  have hc := P.assignedTopReference_physical_center packets assigned top oldSlope newSlope
    R cone w F hw hcone hF hwide hfrequency j l
  have he : (Q).rowSlope j l = oldSlope+P.rowSlope j (orig j l).val.2-newSlope := by
    linarith
  rw [he]
  exact hs

theorem assignedTopReference_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (l : (Q).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l).val.2) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l).val.2 u.val :=
  (P.assignedTopFamily packets assigned top).referenceFamily_physicalMultiplierCoefficient oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency (P.assignedTopSelector packets assigned top b) v f j l u

end Reference

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
