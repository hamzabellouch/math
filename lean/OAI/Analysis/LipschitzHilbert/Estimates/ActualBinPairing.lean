import OAI.Analysis.LipschitzHilbert.Estimates.ActualBinReconstruction

namespace OAI

/-! Exact diagonalization in the bilinear pairing, with the actual error
sum and the same bin projections on the input and test. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem positive_band_abs_bound (f : SchwartzMap (ℝ×ℝ) ℂ) (w c C : ℝ)
    (hw : 0<w) (hc : 0<c)
    (hband : ∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C) :
    ∀ omega, planarFourier f omega≠0 → |omega.2|≤C/w := by
  intro omega h
  obtain ⟨hlo,hhi⟩ := hband omega h
  have hnonneg : 0≤omega.2 := by nlinarith
  rw [abs_of_nonneg hnonneg]
  exact (le_div_iff₀ hw).2 (by nlinarith)

theorem actualBin_pairing (k : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength w W c C : ℝ) (htop : 0<topLength) (hw : 0<w) (hW : 0<W)
    (hc : 0<c) (hC : 0<C) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (hband : ∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C) :
    let J := ⌈C*W/w⌉₊
    let I := verticalBinLabels J w W c C
    (∫ z, shortSlopeOperator (finiteTimeKernel k N topLength) u f z*star (g z) ∂planeMeasure)=
      (∑ n : I, ∫ z, shortSlopeOperator (finiteTimeKernel k N topLength) u
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f) z*
          star (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) g z)
            ∂planeMeasure)-
        ∫ z, totalProjectedBinError k N topLength w W c C u f z*star (g z) ∂planeMeasure := by
  intro J I
  let T := finiteTimeKernel k N topLength
  let P := fun n : I => schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f
  let A := fun n : I => shortSlopeOperator T u (P n)
  let Q := fun n : I => verticalConvolution (verticalProfileKernel verticalBinProfile W
    (verticalBinCenter J W n)) (A n)
  have hTi : Integrable T := finiteTimeKernel_integrable k N topLength htop
  have hTm : Measurable T := finiteTimeKernel_measurable k N topLength
  have hA (n : I) : MemLp (A n) 2 planeMeasure :=
    (shortSlopeOperator_energy T hTm hTi u hu (P n) (P n).continuous.measurable
      ((P n).memLp 2 planeMeasure)).1
  have hAm (n : I) : Measurable (A n) :=
    shortSlopeOperator_measurable T hTm u hu.continuous.measurable (P n) (P n).continuous.measurable
  have hQ (n : I) : MemLp (Q n) 2 planeMeasure :=
    (verticalConvolution_energy_bound _ (verticalProfileKernel_integrable _ W _ hW)
      (verticalProfileKernel_continuous _ W _).measurable (A n) (hAm n) (hA n)).1
  have hi (n : I) : Integrable (fun z => Q n z*star (g z)) planeMeasure :=
    (hQ n).integrable_mul (g.memLp 2 planeMeasure).star
  have hI : I⊆Finset.range (2*J+1) := Finset.filter_subset _ _
  have hE : MemLp (totalProjectedBinError k N topLength w W c C u f) 2 planeMeasure :=
    (totalBinError_energy k N J I hI topLength W htop hW u hu f (C/w) (by positivity)
      (positive_band_abs_bound f w c C hw hc hband)).1
  have hie : Integrable (fun z => totalProjectedBinError k N topLength w W c C u f z*
      star (g z)) planeMeasure := hE.integrable_mul (g.memLp 2 planeMeasure).star
  have hp (z : ℝ×ℝ) : shortSlopeOperator T u f z*star (g z)=
      (∑ n : I, Q n z*star (g z))-
        totalProjectedBinError k N topLength w W c C u f z*star (g z) := by
    rw [actualBin_reconstruction k N topLength w W c C htop hw hW hc u
      hu.continuous.measurable f hband z,sub_mul,Finset.sum_mul]
  calc
    _ = ∫ z, (∑ n : I, Q n z*star (g z))-
        totalProjectedBinError k N topLength w W c C u f z*star (g z) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hp)
    _ = (∑ n : I, ∫ z, Q n z*star (g z) ∂planeMeasure)-
        ∫ z, totalProjectedBinError k N topLength w W c C u f z*star (g z) ∂planeMeasure := by
      rw [integral_sub (integrable_finsetSum _ (fun n _ => hi n)) hie,
        integral_finsetSum _ (fun n _ => hi n)]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      have h := physicalBin_adjoint J W hW n (A n) g (hAm n) g.continuous.measurable
        (hA n) (g.memLp 2 planeMeasure)
      simpa only [←schwartzVerticalProjection_eq_convolution verticalBinProfile W
        (verticalBinCenter J W n) hW g] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
