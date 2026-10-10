import Mathlib
import OAI.Probability.BinarySweep.Representations.IsotypicProjectionMoment
import OAI.Probability.BinarySweep.FiniteLaws.LinearEvenMoment
import OAI.Probability.BinarySweep.FiniteLaws.IndependentPush

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation TraceHolder Density

lemma matrixMoment_linear {I : Type*} [Fintype I] [DecidableEq I]
    (q : ℕ) (M : Matrix I I ℂ) : matrixMoment q M=evenMoment q M.toEuclideanLin := by
  unfold matrixMoment evenMoment
  rw [← trace_toEuclideanLinear]
  simp only [euclidean_pow,Matrix.toLpLin_mul_same,←Module.End.mul_eq_comp,
    Matrix.star_eq_conjTranspose,Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

namespace Signed
variable {A X : Type*} [Fintype A] [DecidableEq A] [Fintype X] {N : ℕ}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def sampleMatrix (p : A → Bool) (w : X → ℂ) (f : X → Equiv.Perm (Fin N)) :=
  ∑x, w x • actionMatrix p (f x)

lemma sampleMatrix_linear (p : A → Bool) (w : X → ℂ) (f : X → Equiv.Perm (Fin N)) :
    (sampleMatrix p w f).toEuclideanLin=∑x, w x • hilbertTensorRep p N (f x) := by
  simp only [sampleMatrix,map_sum,map_smul,actionMatrix_linear]

lemma sampleMatrix_average (p : A → Bool) (w : X → ℂ) (f : X → Equiv.Perm (Fin N)) :
    sampleMatrix p w f=signedAverage p (finitePush w f) := by
  exact (finitePush_expectation w f (actionMatrix p)).symm

omit [FiniteDimensional ℂ V] in
lemma sampleMatrix_commute (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) (w : X → ℂ) (f : X → Equiv.Perm (Fin N)) :
    isotypicProjection p ρ*sampleMatrix p w f=sampleMatrix p w f*isotypicProjection p ρ := by
  rw [sampleMatrix_average]; exact isotypicProjection_commutes_average p ρ _

lemma sample_projected_moment (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) (w : X → ℂ) (f : X → Equiv.Perm (Fin N)) {q : ℕ} (hq : 0<q) :
    matrixMoment q (isotypicProjection p ρ*sampleMatrix p w f)=
      (Module.finrank ℂ (IntertwiningMap ρ (hilbertTensorRep p N)):ℝ)*
        evenMoment q (∑x, w x • ρ (f x)) := by
  rw [sampleMatrix_average,local_projected_moment p ρ hρ _ hq]
  rw [groupAverage,finitePush_expectation]

lemma sampleMoment_le_projected (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖)
    (hocc : 0<Module.finrank ℂ (IntertwiningMap ρ (hilbertTensorRep p N)))
    (w : X → ℂ) (f : X → Equiv.Perm (Fin N)) {q : ℕ} (hq : 0<q) :
    evenMoment q (∑x, w x • ρ (f x))≤
      matrixMoment q (isotypicProjection p ρ*sampleMatrix p w f) := by
  rw [sample_projected_moment p ρ hρ w f hq]
  exact le_mul_of_one_le_left (evenMoment_nonneg _ _) (by exact_mod_cast hocc)

end Signed
end BinaryCoordinateSweeps

end

end OAI
