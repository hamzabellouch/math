import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReferenceProperties
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReferenceCross
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedSum
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalSingleScale

namespace OAI

/-! Absolute single-scale summation is local in angle.  The original
packet family need not have small shear: only the packets being summed
must belong to the displayed reference cone. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem cone_single_scale_cross_packets
    (horder : 6 ≤ P.order)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t s R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (j : Fin N) (d radius M : ℝ) (K H : ℕ)
    (hd : 0 < d) (hM : 0 ≤ M) (hK : radius ≤ K)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d H)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ l k, Measurable (b j l k))
    (hbM : ∀ l k x, ‖b j l k x‖ ≤ M)
    (hsupport : ∀ l k x, b j l k x ≠ 0 → |x-(t+P.rowSlope j l)| ≤ radius*d)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (S : Finset P.PacketIndex)
    (hS : ∀ u ∈ S, P.referenceCondition t s R cone w u.1 u.2.1)
    (z : ℝ×ℝ) :
    (∑ u ∈ S.filter (fun u => u.1 = j), ‖P.crossPacketValue alt hAlt t b v g z u‖) ≤
      P.referenceEnvelopeConstant*((64*(4*Real.pi)^2)*
        ((P.referenceEnvelopeConstant*M*((2*K+1)*H:ℕ))*Real.pi^2)) := by
  let Q := P.referenceFamily t s R cone w F hw hcone hF hwide hfrequency
  let orig := P.referenceOriginalLabel t s R cone w
  let selected := (Finset.univ : Finset Q.PacketIndex).filter
    (fun u => (⟨u.1,orig u.1 u.2.1,u.2.2⟩ : P.PacketIndex) ∈ S)
  have hsum := P.sum_referenceFamily_selected t s R cone w F hw hcone hF hwide hfrequency
    (S.filter (fun u => u.1 = j)) (fun u => ‖P.crossPacketValue alt hAlt t b v g z u‖)
    (fun u hu => hS u (Finset.mem_filter.mp hu).1)
  have hfilter : selected.filter (fun u => u.1 = j) =
      (Finset.univ : Finset Q.PacketIndex).filter (fun u =>
        (⟨u.1,orig u.1 u.2.1,u.2.2⟩ : P.PacketIndex) ∈ S.filter (fun u => u.1 = j)) := by
    ext u
    simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hsum, ← hfilter]
  have heq (u : Q.PacketIndex) := P.referenceFamily_crossPacketValue t s R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v g u.1 u.2.1 u.2.2 z
  simp_rw [← heq]
  exact Q.physical_single_scale_cross_packets
    (P.referenceAlt t s R cone w F hw hcone hF hwide hfrequency alt)
    (P.referenceAlt_bound t s R cone w F hw hcone hF hwide hfrequency alt hAlt)
    horder 0 j s d radius M K H hd hM hK
    (P.referenceFamily_localMultiplicity t s R cone w F hw hcone hF hwide hfrequency j d H hlocal)
    (P.referenceSelector t s R cone w F hw hcone hF hwide hfrequency b)
    (fun l k => hb (orig j l) k) (fun l k x => hbM (orig j l) k x)
    (by
      intro l k x hx
      rw [P.referenceFamily_physical_center t s R cone w F hw hcone hF hwide hfrequency]
      exact hsupport (orig j l) k x hx)
    v hv g hg hg1 selected z

end LipschitzHilbert.PacketLatticeData

end

end OAI
