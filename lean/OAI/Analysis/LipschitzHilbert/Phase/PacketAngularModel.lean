import OAI.Analysis.LipschitzHilbert.Estimates.OrdinaryModelConstruction
import OAI.Analysis.LipschitzHilbert.Phase.PacketAngularAssignment

namespace OAI

/-! Build the three actual ordinary models from one angular assignment.
The assignment is common to all carrier components. It only partitions
the original packet indices; every physical wave and site is preserved. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def angularPackets (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
    (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice) (g : DyadicLineGrid.GridChoice) :
    Finset P.PacketIndex := initial.filter (fun a => tag a.1 a.2.1=g)

def angularSelector (P : PacketLatticeData N κ Label Item)
    (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice) (g : DyadicLineGrid.GridChoice)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (j : Fin N) (l : P.labels j) (k : κ) (s : ℝ) : ℂ :=
  if tag j l=g then b j l k s else 0

def angularModelConfig (P : PacketLatticeData N κ Label Item)
    (initial : Finset P.PacketIndex)
    (cStar cEta CEta cb Cv w F radius : ℝ) (M : ℕ)
    (hcStar : 0≤cStar) (hcEta : 0<cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
    (hcb : 0<cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta<cb/4)
    (num : OrdinaryModelNumerics cStar cEta cb radius)
    (hw : 0<w) (hW : w≤P.width) (hF : 0≤F) (hr : 0≤radius)
    (horder : 207≤P.order) (hfreq : ∀ k, |P.frequency k|≤F/w)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice) (cell : ∀ j, P.labels j → ℤ)
    (hcover : ∀ j l,
      (∀ s, |s-P.rowSlope j l|≤radius*(w/P.length j) →
        s∈scaledAngularCell (w/P.topLength) (tag j l).val j.val (cell j l)) ∧
      (∀ xi eta, cEta≤w*eta → |xi+P.rowSlope j l*eta|≤cStar/P.length j →
        Icc (-xi/eta-cb*(w/P.length j)) (-xi/eta+cb*(w/P.length j))⊆
          scaledAngularCell (w/P.topLength) (tag j l).val j.val (cell j l)))
    (spectrum : ∀ j l a k xi et,
      planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta)
    (bin : ∀ j l a k xi et,
      planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (measurable : ∀ j l k, Measurable (b j l k))
    (bounded : ∀ j l k s, ‖b j l k s‖≤1)
    (away : ∀ j l k s, b j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|)
    (radius_bound : ∀ j l k s, b j l k s≠0 → |s-P.rowSlope j l|≤radius*(w/P.length j))
    (near : ∀ j l k s t, |s-t|≤w/P.length j →
      ‖b j l k s-b j l k t‖≤|s-t|/(w/P.length j))
    (g : DyadicLineGrid.GridChoice) : OrdinaryModelConfig P (P.angularPackets initial tag g) := by
  refine ordinaryModelOfGeometry P (P.angularPackets initial tag g)
    cStar cEta CEta cb Cv w F radius M hcStar hcEta hCEta hCv hcb hcbQuarter hsmall num
    hw hW hF hr horder hfreq hlocal cell g.val ?_ spectrum ?_ bin
    (P.angularSelector tag g b) ?_ ?_ ?_ ?_ ?_ ?_
  · intro q hq
    have heq := (Finset.mem_filter.mp hq).2
    have h := (hcover q.1 q.2.1).1 (P.rowSlope q.1 q.2.1) (by
      simpa only [sub_self,abs_zero] using mul_nonneg hr (div_pos hw (P.length_pos q.1)).le)
    simpa only [heq] using h
  · intro q hq k xi et hs
    have heq := (Finset.mem_filter.mp hq).2
    have hspec := spectrum q.1 q.2.1 q.2.2 k xi et hs
    simpa only [heq] using (hcover q.1 q.2.1).2 xi et hspec.2.1 hspec.1
  · intro j l k
    change Measurable (fun s : ℝ => if tag j l=g then b j l k s else 0)
    by_cases h : tag j l=g
    · simpa [angularSelector,h] using measurable j l k
    · simp [h]
  · intro j l k s
    by_cases h : tag j l=g
    · simpa [angularSelector,h] using bounded j l k s
    · simp [angularSelector,h]
  · intro j l k s hs
    by_cases h : tag j l=g
    · exact away j l k s (by simpa [angularSelector,h] using hs)
    · simp [angularSelector,h] at hs
  · intro j l k s hs
    by_cases h : tag j l=g
    · simpa only [h] using (hcover j l).1 s (radius_bound j l k s (by
        simpa [angularSelector,h] using hs))
    · simp [angularSelector,h] at hs
  · intro j l k s hs
    by_cases h : tag j l=g
    · exact radius_bound j l k s (by simpa [angularSelector,h] using hs)
    · simp [angularSelector,h] at hs
  · intro j l k s t hst
    by_cases h : tag j l=g
    · simpa [angularSelector,h] using near j l k s t hst
    · simp only [angularSelector,h,ite_false,sub_self,norm_zero]
      exact div_nonneg (abs_nonneg _) (div_pos hw (P.length_pos j)).le

end LipschitzHilbert.PacketLatticeData

end

end OAI
