import OAI.Analysis.LipschitzHilbert.Trees.SourceCenteredCoefficient
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceMoments

namespace OAI

/-! Exact positive envelopes of the original physical coefficients.
The symmetric cutoff is controlled by the three actual one-sided
reference families, with no exceptional boundary convention. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

def positiveEnvelope (j : Fin N) (u : ι j) (y x : ℝ) : ℝ :=
  lineEnvelope (P.length j*(P.snappedSite j u).1) (P.length j) 3 x*
    lineEnvelope (P.width*(P.snappedSite j u).2) P.width 2 y

theorem positiveEnvelope_nonneg (j : Fin N) (u : ι j) (y x : ℝ) :
    0 ≤ P.positiveEnvelope j u y x :=
  mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

def physicalPositiveScale (s : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) : ℝ :=
  ∑ u, ‖P.physicalCoefficient s d v g j u‖*P.positiveEnvelope j u y x

def physicalCenteredPositiveScale (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) : ℝ :=
  ∑ u, ‖P.physicalCenteredCoefficient s t d v g j u‖*P.positiveEnvelope j u y x

theorem physicalPositiveScale_nonneg (s : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) :
    0 ≤ P.physicalPositiveScale s d v g j y x :=
  Finset.sum_nonneg (fun u _ => mul_nonneg (norm_nonneg _) (P.positiveEnvelope_nonneg j u y x))

theorem physicalCenteredPositiveScale_nonneg (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) :
    0 ≤ P.physicalCenteredPositiveScale s t d v g j y x :=
  Finset.sum_nonneg (fun u _ => mul_nonneg (norm_nonneg _) (P.positiveEnvelope_nonneg j u y x))

theorem physicalCenteredPositiveScale_le (s t : ℝ) (d : Fin N → ℝ) (hd : ∀ j, 0 ≤ d j)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (y x : ℝ) :
    P.physicalCenteredPositiveScale s t d v g j y x ≤
      P.physicalPositiveScale s (fun j => t+d j) v g j y x+
      P.physicalPositiveScale s (fun j => d j-t) (fun z => -v z) g j y x+
      P.physicalPositiveScale s (fun _ => 0) (fun _ => 0) g j y x := by
  unfold physicalCenteredPositiveScale physicalPositiveScale
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  rw [P.physicalCenteredCoefficient_eq s t d hd v hv g hg hg1]
  have h := (norm_sub_le (P.physicalCoefficient s (fun j => t+d j) v g j u+
      P.physicalCoefficient s (fun j => d j-t) (fun z => -v z) g j u)
      (P.physicalCoefficient s (fun _ => 0) (fun _ => 0) g j u)).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  have hmul := mul_le_mul_of_nonneg_right h (P.positiveEnvelope_nonneg j u y x)
  simpa only [add_mul] using hmul

theorem physicalCenteredPositiveScale_square_sum_le (s t : ℝ) (d : Fin N → ℝ)
    (hd : ∀ j, 0 ≤ d j) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y x : ℝ) :
    (∑ j, P.physicalCenteredPositiveScale s t d v g j y x^2) ≤
      3*((∑ j, P.physicalPositiveScale s (fun j => t+d j) v g j y x^2)+
        (∑ j, P.physicalPositiveScale s (fun j => d j-t) (fun z => -v z) g j y x^2)+
        (∑ j, P.physicalPositiveScale s (fun _ => 0) (fun _ => 0) g j y x^2)) := by
  have hpoint (j : Fin N) : P.physicalCenteredPositiveScale s t d v g j y x^2 ≤
      3*(P.physicalPositiveScale s (fun j => t+d j) v g j y x^2+
        P.physicalPositiveScale s (fun j => d j-t) (fun z => -v z) g j y x^2+
        P.physicalPositiveScale s (fun _ => 0) (fun _ => 0) g j y x^2) := by
    let U := P.physicalPositiveScale s (fun j => t+d j) v g j y x
    let D := P.physicalPositiveScale s (fun j => d j-t) (fun z => -v z) g j y x
    let T := P.physicalPositiveScale s (fun _ => 0) (fun _ => 0) g j y x
    have h := P.physicalCenteredPositiveScale_le s t d hd v hv g hg hg1 j y x
    have h0 := P.physicalCenteredPositiveScale_nonneg s t d v g j y x
    change _ ≤ U+D+T at h
    have hs := mul_self_le_mul_self h0 h
    change _ ≤ 3*(U^2+D^2+T^2)
    nlinarith [sq_nonneg (U-D),sq_nonneg (U-T),sq_nonneg (D-T)]
  calc
    _ ≤ ∑ j, 3*(P.physicalPositiveScale s (fun j => t+d j) v g j y x^2+
        P.physicalPositiveScale s (fun j => d j-t) (fun z => -v z) g j y x^2+
        P.physicalPositiveScale s (fun _ => 0) (fun _ => 0) g j y x^2) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = _ := by rw [← Finset.mul_sum]; simp only [Finset.sum_add_distrib]

variable (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

theorem referenceAnalyzedLine_envelope (y : ℝ) (j : Fin N) (u : ι j) (x : ℝ) :
    (P.referenceAnalyzedLine d v hv g hg hg1 y).envelope j u x =
      P.positiveEnvelope j u y (P.topLength*x) := by
  change lineEnvelope (P.referencePlanarFamily.centerX j u)
      (P.referencePlanarFamily.length j) 3 x*
    lineEnvelope (P.referencePlanarFamily.centerZ j u) P.width 2 y = _
  rw [referencePlanarFamily,PlanarPacketFamily.horizontalRescale_centerX,
    PlanarPacketFamily.horizontalRescale_length,PlanarPacketFamily.horizontalRescale_centerZ,
    P.family_centerX,P.family_centerZ,P.family_length,
    lineEnvelope_horizontalDilation _ _ _ _ _ P.topLength_pos.ne']
  rfl

theorem referenceAnalyzedLine_positiveScale (t y x : ℝ) (j : Fin N) :
    (P.referenceAnalyzedLine d (fun z => v (sourceReferenceToPhysical t z))
      (hv.comp (sourceReferenceToPhysical t).measurable)
      (fun z => g (sourceReferenceToPhysical t z))
      (hg.comp (sourceReferenceToPhysical t).measurable) (fun _ => hg1 _) y).positiveScale j x =
      (P.constant*Real.pi^2)⁻¹*P.physicalPositiveScale t d v g j y (P.topLength*x) := by
  unfold LinePacketFamily.positiveScale physicalPositiveScale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [P.referenceAnalyzedLine_coeff,P.family_mainCoefficient_physical,
    P.referenceAnalyzedLine_envelope,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (mul_pos P.constant_pos (pow_pos Real.pi_pos _)))]
  ring

end LipschitzHilbert.SourceLatticePacket

end

end OAI
