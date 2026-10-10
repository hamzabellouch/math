import OAI.Analysis.LipschitzHilbert.Fourier.BandRetainedDecay
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

theorem band_diagonal_finite_amplitude_bound (hVariation : LepingleInput) (hLL : LaceyLiInput)
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
    ∀ (I J : Finset ℤ), (∀ i∈I, 0<planeMeasure.real (amplitudeLevel f i)) →
      (∀ j∈J, 0<planeMeasure.real (amplitudeLevel g j)) →
    ∀ l r widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z, f z≠0 → z.1∈Icc l r) → (∀ z, g z≠0 → z.1∈Icc l r) →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center
        (fun z => field (planeCoordinates z))
        (fun k z => amplitudeApprox f I z k) (amplitudeApprox g J)‖≤
        K*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  classical
  obtain ⟨D,Kr,Lr,hD,hKr,hLr,hret⟩ := band_diagonal_retained_decay hVariation hLL psi beta
    B c C a M hB hc hC ha hM hpsi hbeta C0 hC0
  obtain ⟨Ke,hKe,herror⟩ := band_diagonal_amplitude_error hVariation psi beta
    B c C a M hB hc hC ha hM hpsi hbeta
  obtain ⟨Lt,hLt⟩ := Filter.eventually_atTop.mp (eventually_amplitude_error_decay Qbase Qrate C0 hQbase hQrate)
  refine ⟨D,Kr+Ke,max Lr Lt,hD,by positivity,le_trans hLr (le_max_left _ _),?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 hf1 hg1 F E ratio Q hF hE hr heq hlog
    hQ hQbound hfb hgb hF1 hG1 hF2 hG2 I J hFi hGj
    l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  have hLr' : Lr≤L := (le_max_left _ _).trans hL
  have hLt' : Lt≤L := (le_max_right _ _).trans hL
  have hL0 : 0≤L := by linarith
  let Ip := I.filter (fun i => |Real.log (planeMeasure.real (amplitudeLevel f i)/F)|≤L/4)
  let Jp := J.filter (fun j => |Real.log (planeMeasure.real (amplitudeLevel g j)/E)|≤L/4)
  have hretained := hret L hLr' N κ topLength width w htop hwidth hw hwW htime hlength
    center hlo hhi field hfield hfieldBound f g hfm hgm hf2 hg2 F E ratio hF hE hr heq hlog hF2 hG2
    Ip Jp (fun i hi => hFi i (Finset.mem_filter.mp hi).1)
    (fun j hj => hGj j (Finset.mem_filter.mp hj).1)
    (fun _ hi => (Finset.mem_filter.mp hi).2) (fun _ hj => (Finset.mem_filter.mp hj).2)
    l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  have herr := herror N κ topLength width w htop hwidth hw hwW center hlo hhi
    (fun z => field (planeCoordinates z)) (product_slope_lipschitz field hfield).continuous.measurable
    (fun z => (hfieldBound _).trans (by norm_num)) f g hfm hgm hf2 hg2 hf1 hg1
    F E Q C0 L hF hE hQ hL0 hfb hgb hF1 hG1 hF2 hG2 I J hFi hGj
  have hsmall := hLt L hLt' Q hQ hQbound
  have herr' := herr.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hKe.le)
      (Real.sqrt_nonneg F)) (Real.sqrt_nonneg E))
  have htriangle := norm_sub_norm_le
    (finiteDiagonalBandL1 (N:=N) psi beta topLength width center (fun z => field (planeCoordinates z))
      (fun k z => amplitudeApprox f I z k) (amplitudeApprox g J))
    (finiteDiagonalBandL1 (N:=N) psi beta topLength width center (fun z => field (planeCoordinates z))
      (fun k z => amplitudeApprox f Ip z k) (amplitudeApprox g Jp))
  calc
    _≤Ke*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+Kr*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
      dsimp only [Ip,Jp] at hretained htriangle
      linarith
    _=_ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
