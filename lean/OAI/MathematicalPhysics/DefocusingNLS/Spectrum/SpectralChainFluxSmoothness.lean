import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainFluxSystem
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxLocalSmoothness

namespace OAI

/-! Smoothness of the inhomogeneous flux ODE follows from the leading solution. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFluxFieldSlope_contDiffOn (μ : ℝ → ℝ) (U₀ : ℝ → E₄) (s : Set ℝ)
    (hμ : ContDiffOn ℝ ∞ μ s) (hU₀ : ContDiffOn ℝ ∞ U₀ s) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => spectralFluxFieldSlope (μ p.1) p.1 (U₀ p.1))
      (s ×ˢ univ) := by
  have hm : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => (μ p.1 : ℂ)) (s ×ˢ univ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hμ.comp contDiff_fst.contDiffOn (fun _ hp => hp.1))
  have hr : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => (p.1 : ℂ)^11) (s ×ˢ univ) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn contDiff_fst.contDiffOn).pow 11
  have hV : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => U₀ p.1) (s ×ˢ univ) :=
    hU₀.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)
  exact (contDiffOn_const.prodMk contDiffOn_const).prodMk
    (((hr.mul hm).mul hV.fst.snd).prodMk (((hr.neg.mul hm).mul hV.fst.fst)))

theorem spectralFluxChain_contDiffOn (ell : ℕ) (μ A : ℝ → ℝ)
    (c ζ : ℂ) (l R : ℝ) (hl : 0 < l) (U₀ U : ℝ → E₄)
    (hμ : ∀ α β : ℝ, l < α → β < R → ContDiffOn ℝ ∞ μ (Icc α β))
    (hA : ∀ α β : ℝ, l < α → β < R → ContDiffOn ℝ ∞ A (Icc α β))
    (hpos : ∀ r ∈ Ioo l R, μ r ≠ 0) (hU₀ : ContDiffOn ℝ ∞ U₀ (Ioo l R))
    (hU : ∀ r ∈ Ioo l R, HasDerivAt U
      (spectralFluxField ell (μ r) (A r) c ζ r (U r) + spectralFluxFieldSlope (μ r) r (U₀ r)) r) :
    ContDiffOn ℝ ∞ U (Ioo l R) := by
  intro r hr
  let α := (l+r)/2
  let β := (r+R)/2
  have hα : l < α := by dsimp [α]; linarith [hr.1]
  have hβ : β < R := by dsimp [β]; linarith [hr.2]
  have har : α < r := by dsimp [α]; linarith [hr.1]
  have hrb : r < β := by dsimp [β]; linarith [hr.2]
  have hs : Icc α β ⊆ Ioo l R := fun x hx => ⟨hα.trans_le hx.1,hx.2.trans_lt hβ⟩
  have hc : ContDiffOn ℝ ∞ U (Icc α β) := by
    apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := fun x V => spectralFluxField ell (μ x) (A x) c ζ x V +
        spectralFluxFieldSlope (μ x) x (U₀ x)) (u := (univ : Set E₄))
    · exact (spectralFluxField_contDiffOn ell μ A c ζ (Icc α β)
        (hμ α β hα hβ) (hA α β hα hβ)
        (fun x hx => hpos x (hs hx)) (fun x hx => (hl.trans (hs hx).1).ne')).add
          (spectralFluxFieldSlope_contDiffOn μ U₀ (Icc α β) (hμ α β hα hβ) (hU₀.mono hs))
    · exact fun x hx => (hU x (hs hx)).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
  exact (hc.contDiffAt (Icc_mem_nhds har hrb)).contDiffWithinAt

end DefocusingNLS

end OAI
