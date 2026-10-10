import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledErrorPhysicalTail
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledErrorBudget

namespace OAI

/-! The original physical error tail, uniform before choosing the packet
family and the reference line. Fixed selector multiplicity and Lipschitz
bounds absorb the source-amplitude factor in one polynomial power. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice

/-- Uniform physical error tail with its source-amplitude budget discharged.
The geometric hypotheses are exactly those of the labeled error family. -/
theorem eventually_uniform_physicalAngularError_tail
    (q rate M Lip : ℝ) (hq : 0 ≤ q) (hrate : 0 ≤ rate)
    (hM : 0 ≤ M) (hLip : 0 ≤ Lip) (K H J₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (_horder : 6 ≤ P.order),
      P.absoluteConstant ≤ L^q →
    ∀ (t a c Cwide radius : ℝ) (E J : ℕ)
      (_ha : 0 < a) (_hc : 0 < c) (_hc1 : c ≤ 1)
      (_hC : Cwide ≤ c*(2:ℝ)^J) (_hwide : 1 ≤ Cwide*((2:ℝ)^E)^4)
      (_hradius : radius ≤ K)
      (_hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => t+P.rowSlope j l) (a*(2:ℝ)^j.val) H)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (_hb : ∀ j l k, Measurable (b j l k))
      (_hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
      (_hsupport : ∀ j l k s, b j l k s ≠ 0 →
        |s-(t+P.rowSlope j l)| ≤ radius*(a*(2:ℝ)^j.val))
      (_hnear : ∀ j l k s, |s-t| ≤ c*(a*(2:ℝ)^j.val) →
        ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(a*(2:ℝ)^j.val)))
      (_hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(a*(2:ℝ)^j.val) < |s-t| →
        b j l k s = 0)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
    ∀ (y u W : ℝ), 0 < W → (∀ j (l : P.labels j) (_i : Item j l), P.length j ≤ W) →
      (volume.restrict (Ico u (u+W)))
        {x | L^(q+8) ≤ P.physicalAngularError t a b v g (x,y+t*x)} ≤
          ENNReal.ofReal (Real.exp (-rate*L))*ENNReal.ofReal W := by
  filter_upwards [LabeledAngularErrorFamily.eventually_source_error_physical_tail
      (q+1) rate (by linarith) hrate J₀,
    LabeledAngularErrorFamily.eventually_sourceAmplitude_le K H M Lip q]
    with L htail hbudget
  intro N κ Label Item _ _ P horder hP t a c Cwide radius E J
    ha hc hc1 hC hwide hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1
    hJ hE y u W hW hshort
  let Q := P.angularErrorFamily horder t a c Cwide M Lip radius E J K H ha hc hc1 hC hwide
    hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1
  have hAmp : Q.sourceAmplitude ≤ L^(q+1) :=
    hbudget N (fun j => P.labels j) κ (fun j l => Item j l) Q
      le_rfl le_rfl le_rfl le_rfl hP
  have ht := htail N (fun j => P.labels j) κ (fun j l => Item j l) Q
    hAmp hJ hE y u W hW hshort
  have heq (x : ℝ) : Q.error y x = P.physicalAngularError t a b v g (x,y+t*x) := by
    exact P.angularErrorFamily_error horder t a c Cwide M Lip radius E J K H
      ha hc hc1 hC hwide hM hLip hradius hlocal b hb hbM hsupport hnear hfar v hv g hg hg1 (x,y)
  simpa only [heq,show q+1+7 = q+8 by ring] using ht

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
