import OAI.Analysis.LipschitzHilbert.Packets.AnnularPacketGeometry
import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedAnnularFormL1
import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedSymbolBasicL1
import OAI.Analysis.LipschitzHilbert.Estimates.NormalizedProfileBudget

namespace OAI

/-! The actual finite partitioned annular multiplier has a uniform basic bound.
The fixed symbol and profile costs are constructed, not assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_partitioned_annular_basic_l1 (hVariation : LepingleInput)
    (psi rho beta : SchwartzMap ℝ ℂ) (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ)
    (A B c C a M : ℝ) (p : AnnularPacketGeometry A B c C a M) (multiplicity : ℕ)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hchiA : ∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (hchiB : ∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) [Fintype κ]
      (topLength width w F : ℝ) (htop : 0<topLength) (hwidth : 0<width),
      0<w → p.H*w≤width → 0≤F →
    ∀ (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ),
      (∀ k, |2*Real.pi*center k|≤F/(p.H*w)) →
      (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
        ((p.H*w)/(topLength/(2:ℝ)^j.val)) multiplicity) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ k, Integrable (f k) planeMeasure) → (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
      ‖partitionedAnnularSumL1 psi rho beta chiA chiB topLength width w htop hwidth
        labels theta center u f g‖≤
        K*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
  obtain ⟨q,hq,Cprofile,_Lp,hCp,_hLp,hprofiles,_hbudget⟩ :=
    exists_normalized_profile_budget (planarInverseSchwartz chiA) (planarInverseSchwartz chiB) 0
  obtain ⟨Csymbol,hCs,hS⟩ := partitionedSymbol_uniform psi (dilatedSlopeWindow rho p.H p.H_pos.ne') beta
    (p.H*c) (mul_pos p.H_pos p.hc) p.R p.hR q
  obtain ⟨K,hK,hbasic⟩ := exists_normalized_symbol_basic_l1 hVariation chiA chiB q hq
    A B (2*Real.pi*(p.H*c)) (2*Real.pi*(p.H*C)) p.inner p.outer Cprofile Csymbol
    multiplicity (requiredPacketOrder 0) p.hA p.hB (by positivity [p.H_pos,p.hc])
    (by positivity [p.H_pos,p.hC]) p.inner_pos p.outer_pos p.quarter
    hCp hCs (requiredPacketOrder_basic 0).1 p.separation p.coverage p.numerics
    hchiA hchiB hprofiles
  refine ⟨K,hK,?_⟩
  intro N κ Label _ topLength width w F htop hwidth hw hW hF labels theta center
    hfrequency hlo hhi hlocal u hu f fData g hfint hf hfm hgm hfb hgb E Fset
    hE hFset hEfin hFfin hgs hfs
  have hscaledLo (k : κ) : 2*Real.pi*(p.H*c)+(2*Real.pi*B)*((p.H*w)/width)≤
      (p.H*w)*(2*Real.pi*center k) := by
    convert mul_le_mul_of_nonneg_left (hlo k) (show 0≤2*Real.pi*p.H by positivity [p.H_pos]) using 1 <;> ring
  have hscaledHi (k : κ) : (p.H*w)*(2*Real.pi*center k)+(2*Real.pi*B)*((p.H*w)/width)≤
      2*Real.pi*(p.H*C) := by
    convert mul_le_mul_of_nonneg_left (hhi k) (show 0≤2*Real.pi*p.H by positivity [p.H_pos]) using 1 <;> ring
  rw [←normalizedSymbolSum_eq_partitioned_annular_l1 psi rho beta chiA chiB A B c C a M p.R p.H p.hR p.H_pos
    p.hc p.hC p.ha p.hM p.hA p.narrow hpsi p.size hchiA topLength width w htop hwidth hw
    labels theta center (fun k => p.parameter_bound w width (center k) hw hwidth hW (hlo k) (hhi k))
    hlo hhi u f g]
  exact hbasic N κ Label topLength width (p.H*w) F htop hwidth (mul_pos p.H_pos hw) hW hF
    labels theta center hfrequency hscaledLo hscaledHi hlocal
    (fun _ k => partitionedSymbol psi (dilatedSlopeWindow rho p.H p.H_pos.ne') beta
      (p.H*c) (mul_pos p.H_pos p.hc) p.R p.hR (p.H*w*center k) (p.H*w/width))
    (fun _ k => hS _ _) u hu f fData g hfint hf hfm hgm hfb hgb E Fset
    hE hFset hEfin hFfin hgs hfs

end LipschitzHilbert.PacketRepresentation

end

end OAI
