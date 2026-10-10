import OAI.Analysis.LipschitzHilbert.Phase.FiniteDiagonalHighL1
import OAI.Analysis.LipschitzHilbert.Phase.DiagonalGeometryChoice

namespace OAI

/-! The improved diagonal estimate with all auxiliary geometry removed.
A fixed multiple of the band width specifies the retained low endpoint. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_high_l1 (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ D K L0 : ℝ, 0<D ∧ 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      planeMeasure E≠∞ → planeMeasure Fset≠∞ → 0<planeMeasure.real Fset →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
    ∀ l r ratio widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z∈E, z.1∈Icc l r) → (∀ z∈Fset, z.1∈Icc l r) →
      0<ratio → L/2≤Real.log ratio → Real.log ratio≤2*L →
      planeMeasure.real E=ratio^2*planeMeasure.real Fset →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center
        (fun z => field (planeCoordinates z)) f g‖≤
        K*L^(-20:ℝ)*Real.sqrt (planeMeasure.real Fset)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨A,delta,p,hA,hd,hnarrow⟩ := exists_diagonal_geometry B c C a M hB hc hC ha hM
  obtain ⟨K,L0,hK,hL0,hmain⟩ := exists_finite_diagonal_high_l1 hVariation hLL psi beta
    A B c C a M delta (2*Real.pi*C) (2*Real.pi*c) p hA hB hd hnarrow
    (by positivity) (by positivity) hpsi hbeta
  let D := 4*(p.H+M/c+delta)
  have hD : 0<D := by dsimp only [D]; positivity [p.H_pos]
  refine ⟨D,K,L0,hD,hK,hL0,?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center
    hlo hhi field hfield hfieldBound f fData g hf hfm hgm hfb hgb E Fset
    hE hFset hEfin hFfin hFpos hgs hfs l r ratio widthScale
    hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq hwidthLo hwidthHi hwidthEq
  have hlength' (j : Fin N) : (p.H+M/c+delta)*(w/(topLength/(2:ℝ)^j.val))≤3/4 := by
    have hlen : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
    have hdiv := (div_le_one hlen).mpr (hlength j)
    have heq : D*w/(topLength/(2:ℝ)^j.val)=
        4*((p.H+M/c+delta)*(w/(topLength/(2:ℝ)^j.val))) := by dsimp only [D]; ring
    rw [heq] at hdiv
    linarith
  exact hmain L hL N κ topLength width w htop hwidth hw hwW htime hlength' center
    (fun k => (center_frequency_bounds B c C w width (center k) hB.le hc hw hwidth (hlo k) (hhi k)).1)
    (fun k => (center_frequency_bounds B c C w width (center k) hB.le hc hw hwidth (hlo k) (hhi k)).2)
    hlo hhi field hfield hfieldBound f fData g hf hfm hgm hfb hgb E Fset
    hE hFset hEfin hFfin hFpos hgs hfs l r ratio widthScale
    hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq hwidthLo hwidthHi hwidthEq

end LipschitzHilbert.PacketRepresentation

end

end OAI
