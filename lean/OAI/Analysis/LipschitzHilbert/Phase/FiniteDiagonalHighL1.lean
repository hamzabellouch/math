import OAI.Analysis.LipschitzHilbert.Phase.FiniteDiagonalBandL1
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalWindowRescalingL1
import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedAnnularHighL1
import OAI.Analysis.LipschitzHilbert.Estimates.BoundedSupportedCoordinates
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteSlopeGeometry

namespace OAI

/-! The positive-disparity gain for the actual finite diagonal band.
Only the fixed low scales needed for bounded slope labels are excluded. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_finite_diagonal_high_l1 (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi beta : SchwartzMap ℝ ℂ) (A B c C a M delta F c0 : ℝ)
    (p : AnnularPacketGeometry A B c C a M) (hA : 0<A) (hB : 0<B)
    (hd : 0<delta) (hnarrow : delta*C≤A/2) (hF : 0≤F) (hc0 : 0<c0)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K L0 : ℝ, 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, (p.H+M/c+delta)*(w/(topLength/(2:ℝ)^j.val))≤3/4) →
    ∀ (center : κ → ℝ), (∀ k, c0/w≤|2*Real.pi*center k|) →
      (∀ k, |2*Real.pi*center k|≤F/w) →
      (∀ k, c+B*(w/width)≤w*center k) →
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
  let p' := p.enlargeVertical
  let beta' := verticallyRescaledWindow beta p.H p.H_pos
  let chi := rectangularFrequencyCutoff A (p.H*B) hA (mul_pos p.H_pos hB)
  obtain ⟨multiplicity,hmult⟩ := exists_finiteSlopeCenter_multiplicity delta p.H hd p.H_pos.le
  obtain ⟨K,L0,hK,hL0,hmain⟩ := exists_partitioned_annular_high_l1 hVariation hLL psi
    (scaledSlopePartition delta hd) beta' chi chi A (p.H*B) c C a M p' (p.H*F) (p.H*c0)
    (mul_nonneg p.H_pos.le hF) (mul_pos p.H_pos hc0) multiplicity
    hpsi (rectangularFrequencyCutoff_support A (p.H*B) hA (mul_pos p.H_pos hB))
    (rectangularFrequencyCutoff_support A (p.H*B) hA (mul_pos p.H_pos hB))
  refine ⟨K,L0,hK,hL0,?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center
    hfrequencyLo hfrequency hlo hhi field hfield hfieldBound
    f fData g hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hFpos hgs hfs
    l r ratio widthScale hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq hwidthLo hwidthHi hwidthEq
  let u := fun z : ℝ×ℝ => field (planeCoordinates z)
  have hum : Measurable u := (product_slope_lipschitz field hfield).continuous.measurable
  have hu (z : ℝ×ℝ) : |u z|≤1/4 := hfieldBound _
  have hfint : ∀ k, Integrable (f k) planeMeasure := by
    intro k
    exact (bounded_supported_coordinate_integrable fData hfm hfb Fset hFset hFfin hfs k).congr
      (Filter.Eventually.of_forall (fun z => (hf z k).symm))
  let Krow (j : Fin N) : ℕ := ⌈(1/4)/(delta*(w/(topLength/(2:ℝ)^j.val)))+M/(delta*c)⌉₊
  let labels := fun j : Fin N => finiteSlopeLabels (Krow j)
  let theta := fun (j : Fin N) (n : labels j) =>
    finiteSlopeCenter (Krow j) delta (w/(topLength/(2:ℝ)^j.val)) n.val
  have hlocal (j : Fin N) : SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
      ((p.H*w)/(topLength/(2:ℝ)^j.val)) multiplicity := by
    simpa only [theta,mul_div_assoc] using hmult (Krow j) (w/(topLength/(2:ℝ)^j.val))
      (div_pos hw (div_pos htop (pow_pos (by norm_num) _)))
  have hunit (j : Fin N) (n : labels j) : |theta j n|+(p.H*w)/(topLength/(2:ℝ)^j.val)≤1 := by
    have hh := finiteSlopeCenter_unit_range p.H delta c M (1/4) (w/(topLength/(2:ℝ)^j.val))
      (div_pos hw (div_pos htop (pow_pos (by norm_num) _))) hd p.hc p.hM.le (by norm_num)
      (by linarith [hlength j]) n
    simpa only [theta,mul_div_assoc] using hh
  have hscale (k : κ) : |2*Real.pi*center k|≤(p.H*F)/(p.H*w) := by
    rw [mul_div_mul_left F w p.H_pos.ne']
    exact hfrequency k
  have hscaleLo (k : κ) : (p.H*c0)/(p.H*w)≤|2*Real.pi*center k| := by
    rw [mul_div_mul_left c0 w p.H_pos.ne']
    exact hfrequencyLo k
  have hpad : (p.H*B)*(w/(p.H*width))=B*(w/width) := by field_simp [p.H_pos.ne',hwidth.ne']
  have hlo' (k : κ) : c+(p.H*B)*(w/(p.H*width))≤w*center k := by rw [hpad]; exact hlo k
  have hhi' (k : κ) : w*center k+(p.H*B)*(w/(p.H*width))≤C := by rw [hpad]; exact hhi k
  have hwidthEq' : p.H*width=widthScale*(p'.H*w) := by
    rw [hwidthEq]
    change p.H*(widthScale*w)=widthScale*(p.H*w)
    ring
  have hout := hmain L hL N κ (fun _ : Fin N => ℕ) topLength (p.H*width) w
    htop (mul_pos p.H_pos hwidth) hw (mul_le_mul_of_nonneg_left hwW p.H_pos.le) htime
    labels theta center hscaleLo hscale hlo' hhi' hlocal hunit
    field hfield f fData g hfint hf hfm hgm hfb hgb E Fset hE hFset hEfin hFfin hFpos hgs hfs
    l r ratio widthScale hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq hwidthLo hwidthHi hwidthEq'
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
  rw [finitePartitionedBand_eq_diagonal_l1 psi beta Krow topLength width w delta c M (B/2) (1/4)
    htop hwidth hw hd p.hc p.hM.le hbeta center (fun s hs => (hpsi s hs).2) hbetaband
    (fun j => Nat.le_ceil _) u hum hu f g hfint
    (bounded_supported_coordinate_integrable g hgm hgb E hE hEfin hgs)] at hout
  exact hout

end LipschitzHilbert.PacketRepresentation

end

end OAI
