import OAI.Analysis.LipschitzHilbert.Phase.FiniteDiagonalReverseL1
import OAI.Analysis.LipschitzHilbert.Phase.DiagonalGeometryChoice

namespace OAI

/-! The reverse-disparity diagonal estimate with only the original annular support
and bin hypotheses. All packet geometry is constructed internally. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_reverse_l1 (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      planeMeasure E≠∞ → planeMeasure Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center u f g‖≤
        K*Real.sqrt (planeMeasure.real Fset*planeMeasure.real E)*
          (planeMeasure.real E/planeMeasure.real Fset)^(9/20:ℝ) := by
  obtain ⟨A,delta,p,hA,hd,hnarrow⟩ := exists_diagonal_geometry B c C a M hB hc hC ha hM
  obtain ⟨K,hK,hmain⟩ := exists_finite_diagonal_reverse_l1 hVariation psi beta A B c C a M delta
    p hA hB hd hnarrow hpsi hbeta
  refine ⟨K,hK,?_⟩
  intro N κ _ topLength width w htop hwidth hw hwW center hlo hhi
    u hum hu f fData g hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
  exact hmain N κ topLength width w (2*Real.pi*C) htop hwidth hw hwW (by positivity)
    center (fun k => (center_frequency_bounds B c C w width (center k) hB.le hc hw hwidth (hlo k) (hhi k)).2)
    hlo hhi u hum hu f fData g hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs

end LipschitzHilbert.PacketRepresentation

end

end OAI
