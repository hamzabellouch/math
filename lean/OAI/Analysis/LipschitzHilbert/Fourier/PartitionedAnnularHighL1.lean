import OAI.Analysis.LipschitzHilbert.Packets.AnnularPacketGeometry
import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedAnnularFormL1
import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedSymbolHighL1
import OAI.Analysis.LipschitzHilbert.Estimates.NormalizedProfileBudget

namespace OAI

/-! The full positive-disparity saving for the actual partitioned annular multiplier.
The fixed compact-symbol and profile costs are chosen before every finite
family, and the logarithmic range includes both manuscript endpoints. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_partitioned_annular_high_l1 (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi rho beta : SchwartzMap ℝ ℂ) (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ)
    (A B c C a M : ℝ) (p : AnnularPacketGeometry A B c C a M)
    (F c0 : ℝ) (hF : 0≤F) (hc0 : 0<c0) (multiplicity : ℕ)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hchiA : ∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (hchiB : ∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B) :
    ∃ K L0 : ℝ, 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) [Fintype κ]
      (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width),
      0<w → p.H*w≤width → topLength≤Real.exp (-(L^(97/100:ℝ))) →
    ∀ (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ),
      (∀ k, c0/(p.H*w)≤|2*Real.pi*center k|) →
      (∀ k, |2*Real.pi*center k|≤F/(p.H*w)) →
      (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
        ((p.H*w)/(topLength/(2:ℝ)^j.val)) multiplicity) →
      (∀ j l, |theta j l|+(p.H*w)/(topLength/(2:ℝ)^j.val)≤1) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ k, Integrable (f k) planeMeasure) → (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      0<(volume.prod volume).real Fset →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
    ∀ l r ratio widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z∈E, z.1∈Icc l r) → (∀ z∈Fset, z.1∈Icc l r) →
      0<ratio → L/2≤Real.log ratio → Real.log ratio≤2*L →
      (volume.prod volume).real E=ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*(p.H*w) →
      ‖partitionedAnnularSumL1 psi rho beta chiA chiB topLength width w htop hwidth
        labels theta center (fun z => field (planeCoordinates z)) f g‖≤
        K*L^(-20:ℝ)*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
  obtain ⟨q,hq,Cprofile,_Lp,hCp,_hLp,hprofiles,_hbudget⟩ :=
    exists_normalized_profile_budget (planarInverseSchwartz chiA) (planarInverseSchwartz chiB) 0
  obtain ⟨Csymbol,hCs,hS⟩ := partitionedSymbol_uniform psi (dilatedSlopeWindow rho p.H p.H_pos.ne') beta
    (p.H*c) (mul_pos p.H_pos p.hc) p.R p.hR q
  obtain ⟨K,L0,hK,hL0,hhigh⟩ := exists_normalized_symbol_high_l1 hVariation hLL chiA chiB q hq
    A B (2*Real.pi*(p.H*c)) (2*Real.pi*(p.H*C)) p.inner p.outer Cprofile Csymbol F c0
    multiplicity (requiredPacketOrder 0) p.hA p.hB (by positivity [p.H_pos,p.hc])
    (by positivity [p.H_pos,p.hC]) p.inner_pos p.outer_pos p.quarter
    hCp hCs (requiredPacketOrder_basic 0).1 hF hc0 p.separation p.coverage p.numerics
    hchiA hchiB hprofiles
  refine ⟨K,L0,hK,hL0,?_⟩
  intro L hL N κ Label _ topLength width w htop hwidth hw hW hshort labels theta center
    hfrequencyLo hfrequency hlo hhi hlocal hunitRange field hfield
    f fData g hfint hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hFpos hgs hfs
    l r ratio widthScale hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq hwidthLo hwidthHi hwidthEq
  have hscaledLo (k : κ) : 2*Real.pi*(p.H*c)+(2*Real.pi*B)*((p.H*w)/width)≤
      (p.H*w)*(2*Real.pi*center k) := by
    convert mul_le_mul_of_nonneg_left (hlo k) (show 0≤2*Real.pi*p.H by positivity [p.H_pos]) using 1 <;> ring
  have hscaledHi (k : κ) : (p.H*w)*(2*Real.pi*center k)+(2*Real.pi*B)*((p.H*w)/width)≤
      2*Real.pi*(p.H*C) := by
    convert mul_le_mul_of_nonneg_left (hhi k) (show 0≤2*Real.pi*p.H by positivity [p.H_pos]) using 1 <;> ring
  rw [←normalizedSymbolSum_eq_partitioned_annular_l1 psi rho beta chiA chiB A B c C a M p.R p.H p.hR p.H_pos
    p.hc p.hC p.ha p.hM p.hA p.narrow hpsi p.size hchiA topLength width w htop hwidth hw
    labels theta center (fun k => p.parameter_bound w width (center k) hw hwidth hW (hlo k) (hhi k))
    hlo hhi (fun z => field (planeCoordinates z)) f g]
  exact hhigh L hL N κ Label topLength width (p.H*w) htop hwidth (mul_pos p.H_pos hw) hW hshort
    labels theta center hfrequencyLo hfrequency hscaledLo hscaledHi hlocal hunitRange
    (fun _ k => partitionedSymbol psi (dilatedSlopeWindow rho p.H p.H_pos.ne') beta
      (p.H*c) (mul_pos p.H_pos p.hc) p.R p.hR (p.H*w*center k) (p.H*w/width))
    (fun _ k => hS _ _) field hfield f fData g hfint hf hfm hgm hfb hgb E Fset
    hE hFset hEfin hFfin hFpos hgs hfs
    l r ratio widthScale hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq hwidthLo hwidthHi hwidthEq

end LipschitzHilbert.PacketRepresentation

end

end OAI
