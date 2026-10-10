import OAI.Analysis.LipschitzHilbert.Fourier.BandAmplitudeHigh
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

theorem band_diagonal_retained_amplitude_sum (hVariation : LepingleInput) (hLL : LaceyLiInput)
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
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
    ∀ (F E ratio C0 : ℝ), 0<F → 0<E → 0<ratio → E=ratio^2*F → Real.log ratio=L →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤C0*F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤C0*E →
    ∀ (I J : Finset ℤ), (∀ i∈I, 0<planeMeasure.real (amplitudeLevel f i)) →
      (∀ j∈J, 0<planeMeasure.real (amplitudeLevel g j)) →
      (∀ i∈I, |Real.log (planeMeasure.real (amplitudeLevel f i)/F)|≤L/4) →
      (∀ j∈J, |Real.log (planeMeasure.real (amplitudeLevel g j)/E)|≤L/4) →
    ∀ l r widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z, f z≠0 → z.1∈Icc l r) → (∀ z, g z≠0 → z.1∈Icc l r) →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) •
        finiteDiagonalBandL1 (N:=N) psi beta topLength width center
          (fun z => field (planeCoordinates z))
          (fun k z => amplitudePiece f i z k) (amplitudePiece g j)‖≤
        K*L^(-20:ℝ)*(retainedAmplitudeCost C0 L)^2*Real.sqrt F*Real.sqrt E := by
  obtain ⟨D,K,L0,hD,hK,hL0,hmain⟩ :=
    band_diagonal_retained_amplitude_pair hVariation hLL psi beta B c C a M hB hc hC ha hM hpsi hbeta
  refine ⟨D,K,L0,hD,hK,hL0,?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 F E ratio C0 hF hE hr heq hlog hEf hEg I J
    hFi hGj hlogf hlogg l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  have hL0' : 0≤L := (by linarith : 0≤L0).trans hL
  have hout := retained_amplitude_matrix_bound planeMeasure f g hfm hgm hf2 hg2 I J
    F E C0 C0 (K*L^(-20:ℝ)) L hF hE (by positivity) hL0' hEf hEg hFi hGj
    (fun i hi => (hlogf i hi).trans (by linarith))
    (fun j hj => (hlogg j hj).trans (by linarith))
    (fun i j => finiteDiagonalBandL1 (N:=N) psi beta topLength width center
      (fun z => field (planeCoordinates z))
      (fun k z => amplitudePiece f i z k) (amplitudePiece g j))
    (fun i hi j hj => hmain L hL N κ topLength width w htop hwidth hw hwW htime hlength
      center hlo hhi field hfield hfieldBound f g hfm hgm hf2 hg2 F E ratio hF hE hr heq hlog
      i j (hFi i hi) (hGj j hj) (hlogf i hi) (hlogg j hj)
      l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq)
  convert hout using 1; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
