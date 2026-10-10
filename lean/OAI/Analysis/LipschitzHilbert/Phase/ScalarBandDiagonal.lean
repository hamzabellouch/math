import OAI.Analysis.LipschitzHilbert.Phase.BandDiagonalBasicL1
import OAI.Analysis.LipschitzHilbert.Phase.BandDiagonalReverseL1

namespace OAI

/-! The scalar basic and reverse-disparity diagonal bounds, without
projecting the test or imposing a spectrum on amplitude slices. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

def scalarVector (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : EuclideanSpace ℂ Unit :=
  PiLp.single 2 () (f z)

theorem scalarVector_apply (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) (i : Unit) :
    scalarVector f z i=f z := by
  cases i
  simp only [scalarVector,PiLp.single_apply,ite_true]

theorem scalarVector_norm (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : ‖scalarVector f z‖=‖f z‖ := by
  rw [scalarVector,PiLp.norm_single]

theorem scalarVector_measurable (f : (ℝ×ℝ) → ℂ) (hf : Measurable f) :
    Measurable (scalarVector f) := by
  unfold scalarVector PiLp.single
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro i
  cases i
  simpa only [Pi.single_apply,ite_true] using hf

def scalarBandForm (psi beta : SchwartzMap ℝ ℂ) (N : ℕ) (topLength W center : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f g : (ℝ×ℝ) → ℂ) : ℂ :=
  ∑ j : Fin N, ∫ z, variableFrequencyMultiplierL1
    (annularBandSymbol psi beta (topLength/(2:ℝ)^j.val) W center u) f z*star (g z) ∂planeMeasure

theorem scalarBandForm_eq (psi beta : SchwartzMap ℝ ℂ) (N : ℕ) (topLength W center : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f g : (ℝ×ℝ) → ℂ) :
    scalarBandForm psi beta N topLength W center u f g=
      finiteDiagonalBandL1 (N:=N) psi beta topLength W (fun _ : Unit => center) u
        (fun _ => f) (scalarVector g) := by
  simp only [scalarBandForm,finiteDiagonalBandL1,Fintype.sum_unique,scalarVector_apply]

theorem scalar_band_basic (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (topLength W w center : ℝ),
      0<topLength → 0<W → 0<w → w≤W → c+B*(w/W)≤w*center → w*center+B*(w/W)≤C →
    ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : (ℝ×ℝ) → ℂ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
      ‖scalarBandForm psi beta N topLength W center u f g‖≤
        K*Real.sqrt (planeMeasure.real F)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨K,hK,hmain⟩ := band_diagonal_basic_l1 hVariation psi beta B c C a M hB hc hC ha hM hpsi hbeta
  refine ⟨K,hK,?_⟩
  intro N topLength W w center htop hW hw hwW hlo hhi u hum hu f g hfm hgm hfb hgb
    E F hE hF hEfin hFfin hgs hfs
  rw [scalarBandForm_eq]
  exact hmain N Unit topLength W w htop hW hw hwW (fun _ => center) (fun _ => hlo) (fun _ => hhi)
    u hum hu (fun _ => f) (scalarVector f) (scalarVector g)
    (fun z i => (scalarVector_apply f z i).symm) (scalarVector_measurable f hfm) (scalarVector_measurable g hgm)
    (fun z => by rw [scalarVector_norm]; exact hfb z) (fun z => by rw [scalarVector_norm]; exact hgb z)
    E F hE hF hEfin hFfin
    (fun z hz => by simp only [scalarVector,hgs z hz,PiLp.single_eq_zero_iff])
    (fun z hz => by simp only [scalarVector,hfs z hz,PiLp.single_eq_zero_iff])

theorem scalar_band_reverse (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (topLength W w center : ℝ),
      0<topLength → 0<W → 0<w → w≤W → c+B*(w/W)≤w*center → w*center+B*(w/W)≤C →
    ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : (ℝ×ℝ) → ℂ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
      ‖scalarBandForm psi beta N topLength W center u f g‖≤
        K*Real.sqrt (planeMeasure.real F*planeMeasure.real E)*
          (planeMeasure.real E/planeMeasure.real F)^(9/20:ℝ) := by
  obtain ⟨K,hK,hmain⟩ := band_diagonal_reverse_l1 hVariation psi beta B c C a M hB hc hC ha hM hpsi hbeta
  refine ⟨K,hK,?_⟩
  intro N topLength W w center htop hW hw hwW hlo hhi u hum hu f g hfm hgm hfb hgb
    E F hE hF hEfin hFfin hgs hfs
  rw [scalarBandForm_eq]
  exact hmain N Unit topLength W w htop hW hw hwW (fun _ => center) (fun _ => hlo) (fun _ => hhi)
    u hum hu (fun _ => f) (scalarVector f) (scalarVector g)
    (fun z i => (scalarVector_apply f z i).symm) (scalarVector_measurable f hfm) (scalarVector_measurable g hgm)
    (fun z => by rw [scalarVector_norm]; exact hfb z) (fun z => by rw [scalarVector_norm]; exact hgb z)
    E F hE hF hEfin hFfin
    (fun z hz => by simp only [scalarVector,hgs z hz,PiLp.single_eq_zero_iff])
    (fun z hz => by simp only [scalarVector,hfs z hz,PiLp.single_eq_zero_iff])

end LipschitzHilbert.PacketRepresentation

end

end OAI
