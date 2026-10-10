import OAI.Analysis.LipschitzHilbert.Trees.SourceAmplitudeMeasurable
import OAI.Analysis.LipschitzHilbert.Trees.SourceSnapshotSize
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledTopSum

namespace OAI

/-! The masked physical packet family is measurable in the spatial
point. Its analyzing coefficients are fixed integrals; no continuity of
the direction selector is required. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

private theorem vectorPacketSynthesis_joint_continuous {ι κ : Type*}
    [Fintype ι] [Fintype κ] (c : ι → EuclideanSpace ℂ κ)
    (f : ι → κ → ℝ → SchwartzMap ℝ ℂ)
    (hf : ∀ i k, Continuous (fun z : ℝ × ℝ => f i k z.1 z.2)) :
    Continuous (fun z : ℝ × ℝ => vectorPacketSynthesis c (fun i k => f i k z.1) z.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  simp only [packetSynthesis_apply]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hf i k))

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem rawBand_slope_continuous (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (j : Fin N) (slope : ℝ) :
    Continuous (fun z : ℝ × ℝ => P.rawBand coeff jet j z.1 (z.2-slope*z.1)) := by
  have hc := vectorPacketSynthesis_joint_continuous
    (fun u : Σ l : P.labels j, Item j l => coeff j u.1 u.2)
    (fun u k y => P.raw jet j u.1 u.2 k y)
    (fun u k => modulatedPlanarJet_continuous (P.profile j u.1 u.2 k)
      (P.actualX j u.1 u.2) (P.actualZ j u.1 u.2) (P.length j) P.width
      (-P.rowSlope j u.1) (P.frequency k) P.scale (P.length_pos j).ne' jet)
  have hs := hc.comp
    (show Continuous (fun z : ℝ × ℝ => (z.2-slope*z.1,z.1)) by fun_prop)
  change Continuous (fun z : ℝ × ℝ => vectorPacketSynthesis
    (fun u : Σ l : P.labels j, Item j l => coeff j u.1 u.2)
    (fun u k => P.raw jet j u.1 u.2 k (z.2-slope*z.1)) z.1)
  exact hs

theorem masked_rawBand_continuous (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (T : SlopeBox) (L A : ℝ) (jet : Fin 3) (j : Fin N) :
    Continuous (fun z : ℝ × ℝ =>
      P.rawBand (fun j l u => T.mask L A z • coeff j l u) jet j z.1 (z.2-T.slope*z.1)) := by
  have hc := (T.mask_continuous L A).smul (P.rawBand_slope_continuous coeff jet j T.slope)
  convert hc using 1
  funext z
  exact P.rawBand_coeff_real_smul coeff (T.mask L A z) jet j z.1 (z.2-T.slope*z.1)

end SourceLabeledLattice

namespace AngularGrid

theorem source_masked_amplitude_measurable {ι : Type}
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (P : ι → SourceLabeledLattice N κ Label Item)
    (coeff : ∀ t j (l : (P t).labels j), Item j l → EuclideanSpace ℂ κ)
    (w cut Kw D L maskExponent : ℝ) (hKw : 0 < Kw)
    (Kb : ℕ) (gap : ℕ → ℝ) (stop : ι → Fin N → ℕ)
    (phase : ℕ → ℂ) (a : ℝ) (jet : Fin 3) (level : ℕ) (cell : ℤ) :
    Measurable (fun z : ℝ × ℝ =>
      g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length) cut
        (fun t zz => (T t).weight Kw D zz) Kb gap
        (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
        (fun p => (P p.1).rawBand
          (fun j l u => (T p.1).mask L maskExponent z • coeff p.1 j l u)
          jet p.2 z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell) := by
  apply g.measurable_sourcePacketAmplitude
  · intro t
    exact ((T t).weight_continuous Kw D hKw).measurable
  · intro p
    exact ((P p.1).masked_rawBand_continuous (coeff p.1) (T p.1) L maskExponent jet p.2).measurable

end AngularGrid
end LipschitzHilbert

end

end OAI
