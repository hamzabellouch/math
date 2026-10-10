import OAI.NumberTheory.DirichletL.Detector.Physical
import OAI.NumberTheory.DirichletL.Descent.Completion

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def physicalRowBase (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O→*ℂ :=
  targetMonoid η*conjugateMonoid Xi*reciprocityPhaseMonoid s hs

lemma physicalRowBase_norm (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (hXi : ∀a,‖Xi a‖≤1) (s : O) (hs : Supported (Ideal.span {s})) (a : O) :
    ‖physicalRowBase η Xi s hs a‖≤1 := by
  change ‖(targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a‖≤1
  rw [norm_mul,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)).trans (hXi a))).trans (sexticReciprocityPhase_norm s a)

lemma ray_rowCoefficient_eq_rowTwist (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m f z n : O) (hn : n=m^6*f^4*z)
    (χ : RayCharacter) :
    rayMonoid χ*rowCoefficient η Xi s hs n=
      rowTwist (rayMonoid χ*physicalRowBase η Xi s hs) m f z := by
  subst n
  ext a
  change rayMonoid χ a*((targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a*
      idealRowHom (m^6*f^4*z) (Ideal.span {a}))=
    (rayMonoid χ a*((targetMonoid η a*star (Xi a))*sexticReciprocityPhase s a))*
      idealRowHom (m^6*f^4*z) (Ideal.span {a})
  ring

def wholeIdealMask (S : Finset Id) (D A : Id) : ℂ :=
  if D∣A ∧ ∀P∈S,¬P∣A then 1 else 0

lemma markedCompletedT_eq_inverse (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    ProbeCompleted.markedCompletedT S D Ψ W X=
      InverseMoment.markedCompletedT Ψ W X (wholeIdealMask S D) := by
  rw [InverseMoment.markedCompletedT_eq_tsum Ψ W hW X hX]
  unfold ProbeCompleted.markedCompletedT
  apply tsum_congr
  intro p
  change completedMask S D p.1 p.2*summand Ψ W X p.1 p.2=
    summand Ψ W X p.1 p.2*wholeIdealMask S D (p.1*p.2^3)
  exact mul_comm _ _

theorem correctedPhysicalRow_eq_inverse_rows (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m f z n : O) (hn : n=m^6*f^4*z)
    (S : Finset Id) (D : Id) (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    correctedCompletedT S D (rowCoefficient η Xi s hs n) W X=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT (rowTwist (rayMonoid χ*physicalRowBase η Xi s hs) m f z)
          W X (wholeIdealMask S D) := by
  rw [correctedCompletedT_ray_expansion S D _ W hW X hX]
  apply Finset.sum_congr rfl
  intro χ _
  rw [markedCompletedT_eq_inverse S D _ W hW X hX,ray_rowCoefficient_eq_rowTwist η Xi s hs m f z n hn χ]

end SevenEighths.ProbePhysical
end

end OAI
