import OAI.NumberTheory.Ostmann.Construction.RemainingRows
import OAI.NumberTheory.Ostmann.Construction.SourcePositive

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem actualAmplitude_row_identity (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (l : ℕ) :
    actualAmplitude sources seed V giant spectator m X G
      (residueTransform d) (favorableGiantResidueTransform d P) bins l =
    (spectatorPrior spectator m).cmean (fun ds =>
      giant.law.cmean (fun p =>
        (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).cmean (fun u =>
          ∑t,guardedFavorableHalfRow d P (outsideProduct (spectatorList spectator ds)) p.val
              (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u) t *
            remainingRow d P sources seed V giant X G bins (spectatorList spectator ds) l p.val u t))) := by
  unfold actualAmplitude
  apply congrArg (FinitePrior.cmean (spectatorPrior spectator m))
  funext ds
  dsimp only
  have hr (p : giant.Sample)
      (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l))) :=
    remainingRow_pairing d P sources seed V giant X G bins (spectatorList spectator ds) l p.val
      (giant.prime _ p.property).pos u
  simp_rw [hr]
  exact outerPrior_extract sources (l+1) (Template.current seed l) giant
    (fun p q small => ∑v:AllowedFrequency V l,
      regularTransform (residueTransform d) (favorableGiantResidueTransform d P)
        (spectatorList spectator ds) ⟨v.val,p,q,small⟩ *
      actualCoefficient sources seed V X G (residueTransform d) bins
        (spectatorList spectator ds) l ⟨v.val,p,q,small⟩)

theorem actualAmplitude_prime_row_bound (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (l : ℕ) :
    ‖actualAmplitude sources seed V giant spectator m X G
      (residueTransform d) (favorableGiantResidueTransform d P) bins l‖^2 ≤
    (spectatorPrior spectator m).mean (fun ds =>
      giant.law.mean (fun p =>
        (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).mean (fun u =>
          (halfProduct p.val (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u):ℝ)*
            ∑t,‖remainingRow d P sources seed V giant X G bins
              (spectatorList spectator ds) l p.val u t‖^2))) := by
  rw [actualAmplitude_row_identity]
  refine ((spectatorPrior spectator m).norm_cmean_sq_le _).trans
    ((spectatorPrior spectator m).mean_mono fun ds => ?_)
  refine (giant.law.norm_cmean_sq_le _).trans (giant.law.mean_mono fun p => ?_)
  refine ((assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).norm_cmean_sq_le _).trans
    ((assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).mean_mono fun u => ?_)
  refine (row_cauchy _ _).trans (mul_le_mul_of_nonneg_right ?_
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  exact guardedFavorableHalfRow_sq_norm_le d P _ _ _
    (halfModuli_prime _ _ (giant.prime _ p.property) (assignedSlots_prime sources _ u))

end Ostmann.Construction

end

end OAI
