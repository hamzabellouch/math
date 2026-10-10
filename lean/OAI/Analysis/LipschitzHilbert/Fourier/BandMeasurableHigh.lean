import OAI.Analysis.LipschitzHilbert.Fourier.BandFiniteAmplitudeBound
import OAI.Analysis.LipschitzHilbert.Phase.DiagonalAmplitudeLimit
import OAI.Analysis.LipschitzHilbert.Fourier.BandAmplitudeError
import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeErrorDecay
import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeRetainedDecay
import OAI.Analysis.LipschitzHilbert.Phase.DiagonalAmplitudeReconstruction
import OAI.Analysis.LipschitzHilbert.Estimates.RetainedAmplitudeMatrix
import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeDisparity
import OAI.Analysis.LipschitzHilbert.Estimates.RestrictedStrongForm

namespace OAI

/-! The improved diagonal estimate applies directly to the manuscript's
measurable normalized amplitude slices; no smoothness of a slice is needed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_measurable_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) (C0 Qbase Qrate : ℝ) (hC0 : 0<C0) (hQbase : 0<Qbase) (hQrate : 0≤Qrate) :
    ∃ D K L0 : ℝ, 0<D ∧ 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (center : κ → ℝ), (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
      Integrable (fun z => ‖f z‖) planeMeasure → Integrable (fun z => ‖g z‖) planeMeasure →
    ∀ (F E ratio Q : ℝ), 0<F → 0<E → 0<ratio → E=ratio^2*F → Real.log ratio=L →
      0≤Q → Q≤Qbase*Real.exp (Qrate*L^(9/10:ℝ)) →
      (∀ z, ‖f z‖≤Q) → (∀ z, ‖g z‖≤Q) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤Q*F → (∫ z, ‖g z‖ ∂planeMeasure)≤Q*E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤C0*F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤C0*E →
    ∀ l r widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z, f z≠0 → z.1∈Icc l r) → (∀ z, g z≠0 → z.1∈Icc l r) →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center
        (fun z => field (planeCoordinates z))
        (fun k z => f z k) g‖≤
        K*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  obtain ⟨D,K,L0,hD,hK,hL0,hmain⟩ := band_diagonal_finite_amplitude_bound hVariation hLL
    psi beta B c C a M hB hc hC ha hM hpsi hbeta C0 Qbase Qrate hC0 hQbase hQrate
  refine ⟨D,K,L0,hD,hK,hL0,?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 hf1 hg1 F E ratio Q hF hE hr heq hlog
    hQ hQbound hfb hgb hF1 hG1 hF2 hG2
    l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  have hf1' : Integrable f planeMeasure := hf1.mono' hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => le_refl _))
  have hg1' : Integrable g planeMeasure := hg1.mono' hgm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => le_refl _))
  have hlim := finiteDiagonalBand_amplitude_limit (N:=N) psi beta topLength width M (B/2) (1/4)
    htop hwidth (fun s hs => (hpsi s hs).2) hbeta center
    (fun z => field (planeCoordinates z)) (product_slope_lipschitz field hfield).continuous.measurable
    (fun z => hfieldBound _) f g hfm hgm hf1' hg1' hf2 hg2
  apply le_of_tendsto hlim.norm
  apply Filter.Eventually.of_forall
  intro n
  exact hmain L hL N κ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 hf1 hg1 F E ratio Q hF hE hr heq hlog
    hQ hQbound hfb hgb hF1 hG1 hF2 hG2
    ((Finset.Icc (-(n:ℤ)) n).filter (fun i => 0<planeMeasure.real (amplitudeLevel f i)))
    ((Finset.Icc (-(n:ℤ)) n).filter (fun j => 0<planeMeasure.real (amplitudeLevel g j)))
    (fun _ hi => (Finset.mem_filter.mp hi).2) (fun _ hj => (Finset.mem_filter.mp hj).2)
    l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq

end LipschitzHilbert.PacketRepresentation

end

end OAI
