import OAI.Analysis.LipschitzHilbert.Phase.BandDiagonalBasicL1
import OAI.Analysis.LipschitzHilbert.Phase.DiagonalAmplitudeReconstruction
import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeMatrixNormalization
import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeTailCost

namespace OAI

/-! The actual diagonal form changes by a controlled amount when all
logarithmically discarded amplitude levels are removed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem band_diagonal_amplitude_error (hVariation : LepingleInput)
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
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
      Integrable (fun z => ‖f z‖) planeMeasure → Integrable (fun z => ‖g z‖) planeMeasure →
    ∀ (F E Q C0 L : ℝ), 0<F → 0<E → 0≤Q → 0≤L →
      (∀ z, ‖f z‖≤Q) → (∀ z, ‖g z‖≤Q) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤Q*F → (∫ z, ‖g z‖ ∂planeMeasure)≤Q*E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤C0*F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤C0*E →
    ∀ (I J : Finset ℤ), (∀ i∈I, 0<planeMeasure.real (amplitudeLevel f i)) →
      (∀ j∈J, 0<planeMeasure.real (amplitudeLevel g j)) →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center u
          (fun k z => amplitudeApprox f I z k) (amplitudeApprox g J)-
        finiteDiagonalBandL1 (N:=N) psi beta topLength width center u
          (fun k z => amplitudeApprox f
            (I.filter (fun i => |Real.log (planeMeasure.real (amplitudeLevel f i)/F)|≤L/4)) z k)
          (amplitudeApprox g (J.filter (fun j => |Real.log (planeMeasure.real (amplitudeLevel g j)/E)|≤L/4)))‖≤
        K*(amplitudeTailCost Q L*(retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L)+
          (retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L)*amplitudeTailCost Q L)*
          Real.sqrt F*Real.sqrt E := by
  obtain ⟨K,hK,hmain⟩ := band_diagonal_basic_l1 hVariation psi beta B c C a M
    hB hc hC ha hM hpsi hbeta
  refine ⟨K,hK,?_⟩
  intro N κ _ topLength width w htop hwidth hw hwW center hlo hhi u hum hu
    f g hfm hgm hf2 hg2 hf1 hg1 F E Q C0 L hF hE hQ hL hfb hgb hF1 hG1 hF2 hG2 I J hFi hGj
  let P := fun i => |Real.log (planeMeasure.real (amplitudeLevel f i)/F)|≤L/4
  let R := fun j => |Real.log (planeMeasure.real (amplitudeLevel g j)/E)|≤L/4
  let aa := fun i => (2:ℝ)^i*Real.sqrt (planeMeasure.real (amplitudeLevel f i)/F)
  let bb := fun j => (2:ℝ)^j*Real.sqrt (planeMeasure.real (amplitudeLevel g j)/E)
  let pair := fun i j => finiteDiagonalBandL1 (N:=N) psi beta topLength width center u
    (fun k z => amplitudePiece f i z k) (amplitudePiece g j)
  have hpair (i j : ℤ) : ‖pair i j‖≤
      K*Real.sqrt (planeMeasure.real (amplitudeLevel f i))*Real.sqrt (planeMeasure.real (amplitudeLevel g j)) :=
    hmain N κ topLength width w htop hwidth hw hwW center hlo hhi u hum hu
      (fun k z => amplitudePiece f i z k) (amplitudePiece f i) (amplitudePiece g j)
      (fun _ _ => rfl) (amplitudePiece_measurable hfm i) (amplitudePiece_measurable hgm j)
      (amplitudePiece_bounded f i) (amplitudePiece_bounded g j)
      (amplitudeLevel g j) (amplitudeLevel f i)
      (amplitudeLevel_measurable hgm.norm j) (amplitudeLevel_measurable hfm.norm i)
      (amplitudeLevel_finite planeMeasure hg2 j) (amplitudeLevel_finite planeMeasure hf2 i)
      (amplitudePiece_supported g j) (amplitudePiece_supported f i)
  have herror := finite_matrix_discard_bound I J P R aa bb
    (fun i j => ((2:ℝ)^i*(2:ℝ)^j) • pair i j) (K*Real.sqrt F*Real.sqrt E)
    (by positivity) (fun _ _ => by dsimp only [aa]; positivity) (fun _ _ => by dsimp only [bb]; positivity)
    (fun i _ j _ => weighted_pair_bound_normalized (pair i j) _ _ K _ _ F E
      (by positivity) (by positivity) measureReal_nonneg measureReal_nonneg hF hE (hpair i j))
  have hsumF := amplitudeLevel_all_weights planeMeasure f hf2 hfm.norm hf1 I F Q C0 L
    hF hQ hL hfb hF1 hF2 hFi
  have hsumG := amplitudeLevel_all_weights planeMeasure g hg2 hgm.norm hg1 J E Q C0 L
    hE hQ hL hgb hG1 hG2 hGj
  have htailF := amplitudeLevel_discarded_sum planeMeasure f hf2 hfm.norm hf1
    (I.filter (fun i => ¬P i)) F Q L hF hQ hfb hF1
    (fun i hi => hFi i (Finset.mem_filter.mp hi).1)
    (fun _ hi => lt_of_not_ge (Finset.mem_filter.mp hi).2)
  have htailG := amplitudeLevel_discarded_sum planeMeasure g hg2 hgm.norm hg1
    (J.filter (fun j => ¬R j)) E Q L hE hQ hgb hG1
    (fun j hj => hGj j (Finset.mem_filter.mp hj).1)
    (fun _ hj => lt_of_not_ge (Finset.mem_filter.mp hj).2)
  rw [finiteDiagonalBand_amplitude_reconstruction psi beta topLength width M (B/2) 1
    htop hwidth (fun s hs => (hpsi s hs).2) hbeta center u hum hu f g hfm hgm hf2 hg2 I J,
    finiteDiagonalBand_amplitude_reconstruction psi beta topLength width M (B/2) 1
    htop hwidth (fun s hs => (hpsi s hs).2) hbeta center u hum hu f g hfm hgm hf2 hg2 (I.filter P) (J.filter R)]
  apply herror.trans
  have hsa : 0≤∑ i∈I, aa i := by dsimp only [aa]; positivity
  have hsb : 0≤∑ j∈J, bb j := by dsimp only [bb]; positivity
  have hta : 0≤∑ i∈I.filter (fun i => ¬P i), aa i := by dsimp only [aa]; positivity
  have htb : 0≤∑ j∈J.filter (fun j => ¬R j), bb j := by dsimp only [bb]; positivity
  have hcost := amplitudeTailCost_nonneg Q L hQ
  calc
    _≤(K*Real.sqrt F*Real.sqrt E)*
        (amplitudeTailCost Q L*(retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L)+
          (retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L)*amplitudeTailCost Q L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul htailF hsumG hsb hcost)
        (mul_le_mul hsumF htailG htb (add_nonneg (retainedAmplitudeCost_nonneg _ _) hcost))
    _=_ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
