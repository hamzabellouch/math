import OAI.Analysis.LipschitzHilbert.Packets.PhysicalPlanarPacket

namespace OAI

/-! The physical covariant derivatives coincide with the three raw
kernels, so their spectral support can be inherited from the full packet. -/

noncomputable section
namespace LipschitzHilbert

theorem physicalPlanarPacket_covariant (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a b l W θ frequency scale : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) :
    (scale:ℂ) • planarCovariantDerivative (physicalPlanarPacket f a b l W θ frequency hl hW) frequency =
      physicalPlanarPacket (((scale/W:ℝ):ℂ) • planarVerticalDerivative f)
        a b l W θ frequency hl hW := by
  ext z
  rcases z with ⟨x,y⟩
  let P := physicalPlanarPacket f a b l W θ frequency hl hW
  have hs (t : ℝ) : planarSchwartzSlice P t 0 =
      modulatedPlanarSlice f a b l W (-θ) frequency t hl := by
    simpa only [zero_mul,sub_zero,zero_sub] using
      physicalPlanarPacket_slice f a b l W θ frequency t 0 hl hW
  have hfun : (fun t => planarSchwartzSlice P t 0 x) =
      (fun t => modulatedPlanarSlice f a b l W (-θ) frequency t hl x) := by
    funext t
    rw [hs t]
  have h := planarCovariantDerivative_slice P frequency scale y 0 x
  rw [hfun,hs y] at h
  have hc := modulatedPlanarSlice_covariant f a b l W (-θ) frequency scale y hl x
  have he := h.symm.trans hc
  have hs' := physicalPlanarPacket_slice (((scale/W:ℝ):ℂ) • planarVerticalDerivative f)
    a b l W θ frequency y 0 hl hW
  have ht := congrArg (fun g : SchwartzMap ℝ ℂ => g x) hs'
  simp only [zero_mul,sub_zero,zero_sub,planarSchwartzSlice_apply,add_zero] at ht he
  exact he.trans ht.symm

theorem physicalPlanarPacket_jet (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a b l W θ frequency scale : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) (i : Fin 3) :
    planarCovariantJet (physicalPlanarPacket f a b l W θ frequency hl hW) frequency scale i =
      physicalPlanarPacket (planarProfileJet f (scale/W) i) a b l W θ frequency hl hW := by
  fin_cases i
  · simp [planarCovariantJet,planarProfileJet]
  · simpa [planarCovariantJet,planarProfileJet] using
      physicalPlanarPacket_covariant f a b l W θ frequency scale hl hW
  · change (scale:ℂ) • planarCovariantDerivative
      ((scale:ℂ) • planarCovariantDerivative
        (physicalPlanarPacket f a b l W θ frequency hl hW) frequency) frequency = _
    rw [physicalPlanarPacket_covariant,physicalPlanarPacket_covariant]
    rfl

theorem physicalPlanarPacket_jet_slice (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a b l W θ frequency scale c s : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) (i : Fin 3) :
    planarSchwartzSlice
      (planarCovariantJet (physicalPlanarPacket f a b l W θ frequency hl hW) frequency scale i) c s =
      modulatedPlanarJet f a (b-s*a) l W (s-θ) frequency scale c hl i := by
  rw [physicalPlanarPacket_jet,physicalPlanarPacket_slice]
  rfl

end LipschitzHilbert

end

end OAI
