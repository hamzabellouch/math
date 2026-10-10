import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Polynomial.Basic

namespace OAI

/-! # The polynomial topology on finite affine coordinates

Points are embedded into the prime spectrum by their evaluation kernels.
This gives a Noetherian T1 topology on finitely many field coordinates.
Polynomial coordinate maps are continuous. This is the topology needed
for the finite-component argument for linear groups.
-/

noncomputable section
namespace PolycyclicRecognition

@[ext]
structure AffinePolynomialPoint (ι K : Type*) where
  coord : ι → K

namespace AffinePolynomialPoint

variable {ι κ K : Type*} [Field K]

def toPrime (x : AffinePolynomialPoint ι K) : PrimeSpectrum (MvPolynomial ι K) :=
  ⟨RingHom.ker (MvPolynomial.eval x.coord), RingHom.ker_isPrime _⟩

instance : TopologicalSpace (AffinePolynomialPoint ι K) :=
  TopologicalSpace.induced toPrime inferInstance

theorem inducing_toPrime : Topology.IsInducing (toPrime (ι := ι) (K := K)) :=
  Topology.IsInducing.induced _

theorem toPrime_injective : Function.Injective (toPrime (ι := ι) (K := K)) := by
  intro x y h
  apply AffinePolynomialPoint.ext
  funext i
  have he := congrArg PrimeSpectrum.asIdeal h
  have hx : MvPolynomial.X i - MvPolynomial.C (x.coord i) ∈ (toPrime x).asIdeal := by
    change MvPolynomial.eval x.coord _ = 0
    simp
  rw [he] at hx
  change MvPolynomial.eval y.coord _ = 0 at hx
  simpa using (sub_eq_zero.mp (by simpa using hx : y.coord i - x.coord i = 0)).symm

instance : T1Space (AffinePolynomialPoint ι K) := by
  constructor
  intro x
  have hclosed : IsClosed ({toPrime x} : Set (PrimeSpectrum (MvPolynomial ι K))) := by
    apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
    exact RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval x.coord)
      (fun a => ⟨MvPolynomial.C a, by simp⟩)
  have he : toPrime ⁻¹' {toPrime x} = ({x} : Set (AffinePolynomialPoint ι K)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, toPrime_injective.eq_iff]
  rw [← he]
  exact hclosed.preimage inducing_toPrime.continuous

instance [Finite ι] : TopologicalSpace.NoetherianSpace (AffinePolynomialPoint ι K) :=
  inducing_toPrime.noetherianSpace

def polynomialMap (p : κ → MvPolynomial ι K) (x : AffinePolynomialPoint ι K) :
    AffinePolynomialPoint κ K :=
  ⟨fun i => MvPolynomial.eval x.coord (p i)⟩

theorem toPrime_polynomialMap (p : κ → MvPolynomial ι K) (x : AffinePolynomialPoint ι K) :
    toPrime (polynomialMap p x) =
      PrimeSpectrum.comap (MvPolynomial.eval₂Hom MvPolynomial.C p) (toPrime x) := by
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro q
  change MvPolynomial.eval (MvPolynomial.eval x.coord ∘ p) q = 0 ↔
    MvPolynomial.eval x.coord (MvPolynomial.eval₂ MvPolynomial.C p q) = 0
  rw [MvPolynomial.eval_assoc]

theorem continuous_polynomialMap (p : κ → MvPolynomial ι K) :
    Continuous (polynomialMap p) := by
  apply inducing_toPrime.continuous_iff.mpr
  have he : toPrime ∘ polynomialMap p =
      PrimeSpectrum.comap (MvPolynomial.eval₂Hom MvPolynomial.C p) ∘ toPrime :=
    funext (toPrime_polynomialMap p)
  rw [he]
  exact (PrimeSpectrum.continuous_comap _).comp inducing_toPrime.continuous

theorem isClosed_zeroSet (p : MvPolynomial ι K) :
    IsClosed {x : AffinePolynomialPoint ι K | MvPolynomial.eval x.coord p = 0} := by
  have he : {x : AffinePolynomialPoint ι K | MvPolynomial.eval x.coord p = 0} =
      toPrime ⁻¹' PrimeSpectrum.zeroLocus {p} := by
    ext x
    change _ ↔ ∀ q ∈ ({p} : Set (MvPolynomial ι K)), q ∈ (toPrime x).asIdeal
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
    rfl
  rw [he]
  exact (PrimeSpectrum.isClosed_zeroLocus _).preimage inducing_toPrime.continuous

end AffinePolynomialPoint
end PolycyclicRecognition

end

end OAI
