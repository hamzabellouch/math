import OAI.Analysis.LipschitzHilbert.Phase.FiniteDiagonalBandL1
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalWindowRescalingL1
import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedAnnularBasicL1
import OAI.Analysis.LipschitzHilbert.Estimates.BoundedSupportedCoordinates

namespace OAI

/-! A uniform basic estimate for the actual finite diagonal band form.
Slope labels, plateaus, compact symbols, and profile budgets are all
constructed inside the proof. The scalar width W=w is included. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_finite_diagonal_basic_l1 (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (A B c C a M delta : ℝ)
    (p : AnnularPacketGeometry A B c C a M) (hA : 0<A) (hB : 0<B)
    (hd : 0<delta) (hnarrow : delta*C≤A/2)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w F : ℝ), 0<topLength → 0<width → 0<w → w≤width → 0≤F →
    ∀ (center : κ → ℝ), (∀ k, |2*Real.pi*center k|≤F/w) →
      (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      planeMeasure E≠∞ → planeMeasure Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center u f g‖≤
        K*Real.sqrt (planeMeasure.real Fset)*Real.sqrt (planeMeasure.real E) := by
  let p' := p.enlargeVertical
  let beta' := verticallyRescaledWindow beta p.H p.H_pos
  let chi := rectangularFrequencyCutoff A (p.H*B) hA (mul_pos p.H_pos hB)
  obtain ⟨multiplicity,hmult⟩ := exists_finiteSlopeCenter_multiplicity delta p.H hd p.H_pos.le
  obtain ⟨K,hK,hmain⟩ := exists_partitioned_annular_basic_l1 hVariation psi
    (scaledSlopePartition delta hd) beta' chi chi A (p.H*B) c C a M p' multiplicity
    hpsi (rectangularFrequencyCutoff_support A (p.H*B) hA (mul_pos p.H_pos hB))
    (rectangularFrequencyCutoff_support A (p.H*B) hA (mul_pos p.H_pos hB))
  refine ⟨K,hK,?_⟩
  intro N κ _ topLength width w F htop hwidth hw hwW hF center hfrequency hlo hhi
    u hum hu f fData g hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
  have hfint : ∀ k, Integrable (f k) planeMeasure := by
    intro k
    exact (bounded_supported_coordinate_integrable fData hfm hfb Fset hFset hFfin hfs k).congr
      (Filter.Eventually.of_forall (fun z => (hf z k).symm))
  let Krow (j : Fin N) : ℕ := ⌈1/(delta*(w/(topLength/(2:ℝ)^j.val)))+M/(delta*c)⌉₊
  let labels := fun j : Fin N => finiteSlopeLabels (Krow j)
  let theta := fun (j : Fin N) (n : labels j) =>
    finiteSlopeCenter (Krow j) delta (w/(topLength/(2:ℝ)^j.val)) n.val
  have hlocal (j : Fin N) : SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
      ((p.H*w)/(topLength/(2:ℝ)^j.val)) multiplicity := by
    simpa only [theta,mul_div_assoc] using hmult (Krow j) (w/(topLength/(2:ℝ)^j.val))
      (div_pos hw (div_pos htop (pow_pos (by norm_num) _)))
  have hscale (k : κ) : |2*Real.pi*center k|≤(p.H*F)/(p.H*w) := by
    rw [mul_div_mul_left F w p.H_pos.ne']
    exact hfrequency k
  have hpad : (p.H*B)*(w/(p.H*width))=B*(w/width) := by field_simp [p.H_pos.ne',hwidth.ne']
  have hlo' (k : κ) : c+(p.H*B)*(w/(p.H*width))≤w*center k := by rw [hpad]; exact hlo k
  have hhi' (k : κ) : w*center k+(p.H*B)*(w/(p.H*width))≤C := by rw [hpad]; exact hhi k
  have hout := hmain N κ (fun _ : Fin N => ℕ) topLength (p.H*width) w (p.H*F)
    htop (mul_pos p.H_pos hwidth) hw (mul_le_mul_of_nonneg_left hwW p.H_pos.le)
    (mul_nonneg p.H_pos.le hF) labels theta center hscale hlo' hhi' hlocal
    u hum f fData g hfint hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hgs hfs
  rw [partitionedAnnularSum_eq_finitePartitionedBand_l1 psi beta' A (p.H*B) c C delta
    hA (mul_pos p.H_pos hB) p.hc hd hnarrow
    (verticallyRescaledWindow_support beta B p.H p.H_pos hbeta)
    topLength (p.H*width) w htop (mul_pos p.H_pos hwidth) hw labels theta center
    hlo' hhi' u f g] at hout
  rw [finitePartitionedBand_vertical_rescaling_l1 psi (scaledSlopePartition delta hd) beta
    p.H p.H_pos topLength width w labels theta center u f g] at hout
  have hbetaband (k : κ) (eta : ℝ) (hb : beta (symbolY width eta (center k))≠0) : c≤w*eta := by
    exact (vertical_annulus_from_window w width (center k) eta B c C hw hwidth
      (hlo k) (hhi k) ((hbeta _ hb).trans (by linarith))).1
  rw [finitePartitionedBand_eq_diagonal_l1 psi beta Krow topLength width w delta c M (B/2) 1
    htop hwidth hw hd p.hc p.hM.le hbeta center (fun s hs => (hpsi s hs).2) hbetaband
    (fun j => Nat.le_ceil _) u hum hu f g hfint
    (bounded_supported_coordinate_integrable g hgm hgb E hE hEfin hgs)] at hout
  exact hout

end LipschitzHilbert.PacketRepresentation

end

end OAI
