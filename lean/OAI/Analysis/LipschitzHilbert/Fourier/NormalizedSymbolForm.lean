import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedConvolutionForm
import OAI.Analysis.LipschitzHilbert.Fourier.FiniteSeparatedSymbolBound
import OAI.Analysis.LipschitzHilbert.Estimates.ScaledUnitSelector

namespace OAI

/-! The original finite normalized symbol form equals the common
weighted average of the actual normalized convolution forms. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

def normalizedSymbolSum (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ)
    (chi : SchwartzMap ℝ ℝ) (topLength width w : ℝ)
    (htop : 0<topLength) (hwidth : 0<width) (labels : ∀ j, Finset (Label j))
    (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (S : LatticeRow labels → κ → SchwartzMap SymbolSpace ℂ)
    (u : ℝ×ℝ → ℝ) (f : κ → SchwartzMap (ℝ×ℝ) ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) : ℂ :=
  ∑ i : LatticeRow labels, ∑ k, ∫ z,
    (chi (symbolU (latticeLength topLength labels i) w (u z) (theta i.1 i.2)):ℂ)*
      (∫ omega, Real.fourierChar (z.1*omega.1+z.2*omega.2) •
        (S i k (symbolPoint (symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2))
          (symbolY width omega.2 (center k))
          (symbolU (latticeLength topLength labels i) w (u z) (theta i.1 i.2)))*
        (latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega*
          latticeFrequencyWindow chiB topLength width htop hwidth labels theta center i k omega*
          planarFourier (f k) omega)) ∂planeMeasure)*star (g z k) ∂planeMeasure

theorem normalized_symbol_sum_eq_average
    (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (chi : SchwartzMap ℝ ℝ)
    (hchi : ∀ s, |chi s|≤1) (C : ℝ) (hC : 0<C) (q : ℕ) (hq : 4≤q)
    (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (S : LatticeRow labels → κ → SchwartzMap SymbolSpace ℂ)
    (hS : ∀ i k, symbolCoefficientBound (S i k) q≤C)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f : κ → SchwartzMap (ℝ×ℝ) ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : ∀ z k, f k z=fData z k) (hg : Measurable g)
    (hgint : ∀ k, Integrable (fun z => g z k) planeMeasure) :
    normalizedSymbolSum chiA chiB chi topLength width w htop hwidth labels theta center S u f g =
      (selectorNormalizer chi C:ℂ)*∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*
        normalizedConvolutionSum chiA chiB q nu topLength width htop hwidth labels theta center
          (fun j l k s => scaledUnitSelector chi C (S ⟨j,l⟩ k) q nu
            (w/(topLength/(2:ℝ)^j.val)) (theta j l) s) u fData g := by
  classical
  let U := fun (i : LatticeRow labels) (z : ℝ×ℝ) =>
    symbolU (latticeLength topLength labels i) w (u z) (theta i.1 i.2)
  have hU (i : LatticeRow labels) : Measurable (U i) := by
    exact (hu.sub measurable_const).div_const _
  have hgm (k : κ) : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  have h := finite_unit_symbol_pairing (ι:=LatticeRow labels × κ) chi hchi C hC
    (fun i => S i.1 i.2) q hq (fun i => hS i.1 i.2)
    (fun i => latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i.1 i.2)
    (fun i => latticeFrequencyWindow chiB topLength width htop hwidth labels theta center i.1 i.2)
    (fun i => f i.2) (fun i => U i.1) (fun i => hU i.1)
    (fun i z => g z i.2) (fun i => hgm i.2) (fun i => hgint i.2)
    (fun i => latticeLength topLength labels i.1) (fun _ => width)
    (fun i => theta i.1.1 i.1.2) (fun i => center i.2)
  simpa only [normalizedSymbolSum,normalizedConvolutionSum,Fintype.sum_prod_type,U,
    scaledUnitSelector,symbolU,latticeLength,←hf] using h


/-- A bound for the entire normalized convolution sum passes through the
same common Fourier weight to the original finite symbol form. -/
theorem normalized_symbol_sum_bound
    (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (chi : SchwartzMap ℝ ℝ)
    (hchi : ∀ s, |chi s|≤1) (C : ℝ) (hC : 0<C) (q : ℕ) (hq : 4≤q)
    (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (S : LatticeRow labels → κ → SchwartzMap SymbolSpace ℂ)
    (hS : ∀ i k, symbolCoefficientBound (S i k) q≤C)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f : κ → SchwartzMap (ℝ×ℝ) ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : ∀ z k, f k z=fData z k) (hg : Measurable g)
    (hgint : ∀ k, Integrable (fun z => g z k) planeMeasure) (bound : ℝ)
    (hbound : ∀ nu : SymbolSpace,
      ‖normalizedConvolutionSum chiA chiB q nu topLength width htop hwidth labels theta center
        (fun j l k s => scaledUnitSelector chi C (S ⟨j,l⟩ k) q nu
          (w/(topLength/(2:ℝ)^j.val)) (theta j l) s) u fData g‖≤bound) :
    ‖normalizedSymbolSum chiA chiB chi topLength width w htop hwidth labels theta center S u f g‖≤
      selectorNormalizer chi C*bound*(∫ nu : SymbolSpace, symbolWeight q nu) := by
  classical
  let U := fun (i : LatticeRow labels) (z : ℝ×ℝ) =>
    symbolU (latticeLength topLength labels i) w (u z) (theta i.1 i.2)
  have hU (i : LatticeRow labels) : Measurable (U i) :=
    (hu.sub measurable_const).div_const _
  have hgm (k : κ) : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  have h := finite_separated_symbol_bound (ι:=LatticeRow labels × κ) chi hchi C hC
    (fun i => S i.1 i.2) q hq (fun i => hS i.1 i.2)
    (fun i => latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i.1 i.2)
    (fun i => latticeFrequencyWindow chiB topLength width htop hwidth labels theta center i.1 i.2)
    (fun i => f i.2) (fun i => U i.1) (fun i => hU i.1)
    (fun i z => g z i.2) (fun i => hgm i.2) (fun i => hgint i.2)
    (fun i => latticeLength topLength labels i.1) (fun _ => width)
    (fun i => theta i.1.1 i.1.2) (fun i => center i.2) bound (by
      intro nu
      simpa only [normalizedConvolutionSum,Fintype.sum_prod_type,U,
        scaledUnitSelector,symbolU,latticeLength,←hf] using hbound nu)
  simpa only [normalizedSymbolSum,Fintype.sum_prod_type,U] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
