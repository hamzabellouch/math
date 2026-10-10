import OAI.Analysis.LipschitzHilbert.Phase.BandDiagonalHighL1
import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeDisparity
import OAI.Analysis.LipschitzHilbert.Estimates.RestrictedStrongForm

namespace OAI

/-! The improved diagonal estimate applies directly to the manuscript's
measurable normalized amplitude slices; no smoothness of a slice is needed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_retained_amplitude_pair (hVariation : LepingleInput) (hLL : LaceyLiInput)
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
    ∀ (F E ratio : ℝ), 0<F → 0<E → 0<ratio → E=ratio^2*F → Real.log ratio=L →
    ∀ (i j : ℤ), 0<planeMeasure.real (amplitudeLevel f i) →
      0<planeMeasure.real (amplitudeLevel g j) →
      |Real.log (planeMeasure.real (amplitudeLevel f i)/F)|≤L/4 →
      |Real.log (planeMeasure.real (amplitudeLevel g j)/E)|≤L/4 →
    ∀ l r widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z, f z≠0 → z.1∈Icc l r) → (∀ z, g z≠0 → z.1∈Icc l r) →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center
        (fun z => field (planeCoordinates z))
        (fun k z => amplitudePiece f i z k) (amplitudePiece g j)‖≤
        K*L^(-20:ℝ)*Real.sqrt (planeMeasure.real (amplitudeLevel f i))*
          Real.sqrt (planeMeasure.real (amplitudeLevel g j)) := by
  obtain ⟨D,K,L0,hD,hK,hL0,hmain⟩ :=
    band_diagonal_high_l1 hVariation hLL psi beta B c C a M hB hc hC ha hM hpsi hbeta
  refine ⟨D,K,L0,hD,hK,hL0,?_⟩
  intro L hL N κ _ topLength width w htop hwidth hw hwW htime hlength center hlo hhi
    field hfield hfieldBound f g hfm hgm hf2 hg2 F E ratio hF hE hr heq hlog i j
    hFi hGj hlogf hlogg l r widthScale hstrip hfstrip hgstrip hwlo hwhi hweq
  obtain ⟨hr',heq'⟩ := sqrt_mass_ratio _ _ hFi hGj
  obtain ⟨hlo',hhi'⟩ := retained_amplitude_disparity F E _ _ ratio L
    hF hE hFi hGj hr heq hlog hlogf hlogg
  apply hmain L hL N κ topLength width w htop hwidth hw hwW htime hlength
    center hlo hhi field hfield hfieldBound
    (fun k z => amplitudePiece f i z k) (amplitudePiece f i) (amplitudePiece g j)
    (fun _ _ => rfl) (amplitudePiece_measurable hfm i) (amplitudePiece_measurable hgm j)
    (amplitudePiece_bounded f i) (amplitudePiece_bounded g j)
    (amplitudeLevel g j) (amplitudeLevel f i)
    (amplitudeLevel_measurable hgm.norm j) (amplitudeLevel_measurable hfm.norm i)
    (amplitudeLevel_finite planeMeasure hg2 j) (amplitudeLevel_finite planeMeasure hf2 i)
    hFi (amplitudePiece_supported g j) (amplitudePiece_supported f i)
    l r (Real.sqrt (planeMeasure.real (amplitudeLevel g j)/planeMeasure.real (amplitudeLevel f i)))
    widthScale hstrip _ _ hr' hlo' hhi' heq' hwlo hwhi hweq
  · intro z hz
    exact hgstrip z (norm_pos_iff.mp ((zpow_pos (by norm_num) _).trans hz.1))
  · intro z hz
    exact hfstrip z (norm_pos_iff.mp ((zpow_pos (by norm_num) _).trans hz.1))

end LipschitzHilbert.PacketRepresentation

end

end OAI
