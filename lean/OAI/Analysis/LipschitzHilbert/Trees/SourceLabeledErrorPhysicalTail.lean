import OAI.Analysis.LipschitzHilbert.Phase.SourceLabeledAngularErrorData
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledErrorTail

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate BigOperators Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item) (horder : 6 ≤ P.order)
  (t a c Cwide M Lip radius : ℝ) (E J K H : ℕ)
  (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1)
  (hC : Cwide ≤ c*(2:ℝ)^J) (hwide : 1 ≤ Cwide*((2:ℝ)^E)^4)
  (hM : 0 ≤ M) (hLip : 0 ≤ Lip) (hradius : radius ≤ K)
  (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
    (fun l => t+P.rowSlope j l) (a*(2:ℝ)^j.val) H)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (hb : ∀ j l k, Measurable (b j l k))
  (hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
  (hsupport : ∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius*(a*(2:ℝ)^j.val))
  (hnear : ∀ j l k s, |s-t| ≤ c*(a*(2:ℝ)^j.val) →
    ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(a*(2:ℝ)^j.val)))
  (hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(a*(2:ℝ)^j.val) < |s-t| → b j l k s = 0)
  (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

/-- The original physical positive error sum has the uniform interval
tail supplied by its actual labeled dyadic family. -/
theorem eventually_physicalAngularError_tail (p rate : ℝ) (hp : 0 ≤ p)
    (hrate : 0 ≤ rate) (J₀ : ℕ) :
    ∀ᶠ L : ℝ in Filter.atTop,
      (P.angularErrorFamily horder t a c Cwide M Lip radius E J K H ha hc hc1 hC hwide
        hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1).sourceAmplitude ≤ L^p →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      ∀ (y u W : ℝ), 0 < W → (∀ j (l : P.labels j) (_i : Item j l), P.length j ≤ W) →
      (volume.restrict (Set.Ico u (u+W)))
        {x | L^(p+7) ≤ P.physicalAngularError t a b v g (x,y+t*x)} ≤
          ENNReal.ofReal (Real.exp (-rate*L))*ENNReal.ofReal W := by
  let Q := P.angularErrorFamily horder t a c Cwide M Lip radius E J K H ha hc hc1 hC hwide
    hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1
  filter_upwards [LabeledAngularErrorFamily.eventually_source_error_physical_tail
    p rate hp hrate J₀] with L htail
  intro hAmp hJ hE y u W hW hshort
  have ht := htail N (fun j => P.labels j) κ (fun j l => Item j l) Q hAmp hJ hE
    y u W hW hshort
  have heq : {x | L^(p+7) ≤ Q.error y x} =
      {x | L^(p+7) ≤ P.physicalAngularError t a b v g (x,y+t*x)} := by
    ext x
    have h := P.angularErrorFamily_error horder t a c Cwide M Lip radius E J K H
      ha hc hc1 hC hwide hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1 (x,y)
    change Q.error y x = P.physicalAngularError t a b v g (x,y+t*x) at h
    change (L^(p+7) ≤ Q.error y x) ↔
      (L^(p+7) ≤ P.physicalAngularError t a b v g (x,y+t*x))
    rw [h]
  rwa [heq] at ht

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
