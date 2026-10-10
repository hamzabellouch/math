import OAI.Analysis.LipschitzHilbert.Fourier.AnnularBandL1
import OAI.Analysis.LipschitzHilbert.Fourier.L1MultiplierLinearity
import OAI.Analysis.LipschitzHilbert.Phase.FiniteDiagonalBandL1
import OAI.Analysis.LipschitzHilbert.Estimates.BoundedSupportedCoordinates
import OAI.Analysis.LipschitzHilbert.Estimates.RestrictedStrongForm

namespace OAI

/-! Exact reconstruction of the actual finite diagonal form from its
measurable amplitude slices. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

variable {κ : Type} [Fintype κ]

theorem amplitudeApprox_coordinate (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (I : Finset ℤ) (z : ℝ×ℝ) (k : κ) :
    amplitudeApprox f I z k=∑ i∈I, (2:ℝ)^i • (amplitudePiece f i z k) := by
  simp only [amplitudeApprox,Finset.sum_apply]
  change WithLp.ofLp (∑ i∈I, (2:ℝ)^i • amplitudePiece f i z) k=_
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply]

theorem amplitudePiece_coordinate_integrable
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hfm : Measurable f) (hf2 : MemLp f 2 planeMeasure)
    (i : ℤ) (k : κ) : Integrable (fun z => amplitudePiece f i z k) planeMeasure :=
  bounded_supported_coordinate_integrable (amplitudePiece f i) (amplitudePiece_measurable hfm i)
    (amplitudePiece_bounded f i) (amplitudeLevel f i) (amplitudeLevel_measurable hfm.norm i)
    (amplitudeLevel_finite planeMeasure hf2 i) (amplitudePiece_supported f i) k

theorem finiteDiagonalBand_amplitude_reconstruction {N : ℕ}
    (psi beta : SchwartzMap ℝ ℂ) (topLength width M B U : ℝ)
    (htop : 0<topLength) (hwidth : 0<width)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (center : κ → ℝ) (u : ℝ×ℝ → ℝ) (hum : Measurable u) (hu : ∀ z, |u z|≤U)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) (hfm : Measurable f) (hgm : Measurable g)
    (hf2 : MemLp f 2 planeMeasure) (hg2 : MemLp g 2 planeMeasure) (I J : Finset ℤ) :
    finiteDiagonalBandL1 (N:=N) psi beta topLength width center u
      (fun k z => amplitudeApprox f I z k) (amplitudeApprox g J)=
      ∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) •
        finiteDiagonalBandL1 (N:=N) psi beta topLength width center u
          (fun k z => amplitudePiece f i z k) (amplitudePiece g j) := by
  classical
  have hU : 0≤U := (abs_nonneg (u 0)).trans (hu 0)
  have hterm (s : Fin N) (k : κ) :
      (∫ z, variableFrequencyMultiplierL1
        (annularBandSymbol psi beta (topLength/(2:ℝ)^s.val) width (center k) u)
        (fun x => amplitudeApprox f I x k) z*star (amplitudeApprox g J z k) ∂planeMeasure)=
      ∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) •
        ∫ z, variableFrequencyMultiplierL1
          (annularBandSymbol psi beta (topLength/(2:ℝ)^s.val) width (center k) u)
          (fun x => amplitudePiece f i x k) z*star (amplitudePiece g j z k) ∂planeMeasure := by
    obtain ⟨q,hq,hbound⟩ := exists_annularBandSymbol_envelope psi beta
      (topLength/(2:ℝ)^s.val) width (center k) M B U
      (div_pos htop (pow_pos (by norm_num) _)) hwidth hU hpsi hbeta u hu
    simp_rw [amplitudeApprox_coordinate]
    rw [variableFrequencyMultiplier_pairing_finset_sum_l1 I J _
      (annularBandSymbol_measurable psi beta _ width (center k) u hum) q hq hbound
      (fun i x => (2:ℝ)^i • amplitudePiece f i x k)
      (fun i _ => (amplitudePiece_coordinate_integrable f hfm hf2 i k).smul ((2:ℝ)^i))
      (fun j x => (2:ℝ)^j • amplitudePiece g j x k)
      (fun j _ => (amplitudePiece_coordinate_integrable g hgm hg2 j k).smul ((2:ℝ)^j))]
    simp only [variableFrequencyMultiplier_pairing_real_smul_l1]
  unfold finiteDiagonalBandL1
  simp_rw [hterm,Finset.smul_sum]
  calc
    _=∑ s : Fin N, ∑ i∈I, ∑ j∈J, ∑ k : κ,
        ((2:ℝ)^i*(2:ℝ)^j) • ∫ z, variableFrequencyMultiplierL1
          (annularBandSymbol psi beta (topLength/(2:ℝ)^s.val) width (center k) u)
          (fun x => amplitudePiece f i x k) z*star (amplitudePiece g j z k) ∂planeMeasure := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _=_ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]

end LipschitzHilbert.PacketRepresentation

end

end OAI
