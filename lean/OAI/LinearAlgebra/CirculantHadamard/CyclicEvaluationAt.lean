import OAI.LinearAlgebra.CirculantHadamard.CyclicEvaluation
import OAI.LinearAlgebra.CirculantHadamard.CyclicPolynomial

namespace OAI

universe uA uS uT

/-!
# Evaluation at an actual root of unity

The algebra map factors through the proved polynomial presentation of the
cyclic group ring and the universal property of `AdjoinRoot (X ^ n - 1)`.
-/

noncomputable section

namespace CirculantHadamard.CyclicRing

open Polynomial
open scoped BigOperators

variable {A : Type uA} {S : Type uS} {T : Type uT} [CommRing A] [CommRing S] [CommRing T]
variable [Algebra A S] [Algebra A T]

/-- Evaluate the polynomial quotient at a proved `n`th root of unity. -/
def evaluateAt (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1) : Elem A n →ₐ[A] S :=
  (AdjoinRoot.liftAlgHom (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx])).comp
      (CyclicPolynomial.cyclicEquiv A n).toAlgHom

@[simp] theorem evaluateAt_single (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1)
    (a : ZMod n) (r : A) :
    evaluateAt n x hx (AddMonoidAlgebra.single a r) = algebraMap A S r * x ^ a.val := by
  change (AdjoinRoot.liftAlgHom (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx]))
      (CyclicPolynomial.cyclicEquiv A n (AddMonoidAlgebra.single a r)) = _
  rw [CyclicPolynomial.cyclicEquiv_single, map_mul, map_pow, AlgHom.commutes,
    AdjoinRoot.liftAlgHom_root (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
      (by simp [CyclicPolynomial.relation, hx])]

@[simp] theorem evaluateAt_scalar (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1)
    (r : A) : evaluateAt n x hx (scalar n r) = algebraMap A S r := by
  simp [scalar]

@[simp] theorem evaluateAt_generator (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1) :
    evaluateAt (A := A) n x hx (CyclicPolynomial.generator A n) = x := by
  change (AdjoinRoot.liftAlgHom (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx]))
      (CyclicPolynomial.cyclicEquiv A n (CyclicPolynomial.generator A n)) = x
  rw [CyclicPolynomial.cyclicEquiv_generator]
  exact AdjoinRoot.liftAlgHom_root (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx])

/-- Evaluation agrees with evaluation of every polynomial in the cyclic generator. -/
@[simp] theorem evaluateAt_aeval (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1)
    (p : A[X]) :
    evaluateAt n x hx (aeval (CyclicPolynomial.generator A n) p) = aeval x p := by
  change (AdjoinRoot.liftAlgHom (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx]))
      (CyclicPolynomial.cyclicEquiv A n (aeval (CyclicPolynomial.generator A n) p)) = _
  rw [CyclicPolynomial.cyclicEquiv_aeval]
  exact AdjoinRoot.liftAlgHom_mk (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx]) p

/-- The quotient construction and the finite-character construction are the same
ring homomorphism. -/
theorem evaluateAt_eq_evaluate (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1) :
    (evaluateAt (A := A) n x hx).toRingHom =
      evaluate (algebraMap A S) (CyclicPolynomial.powerCharacter n x hx) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp [evaluateAt_single]
  · intro a
    simp [evaluateAt_single, CyclicPolynomial.powerCharacter_apply]

theorem evaluateAt_apply (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1)
    (f : Elem A n) :
    evaluateAt n x hx f = ∑ a : ZMod n, algebraMap A S (f.coeff a) * x ^ a.val := by
  change (evaluateAt n x hx).toRingHom f = _
  rw [evaluateAt_eq_evaluate, evaluate_apply]
  rfl

/-- Evaluation at one is the actual augmentation followed by the coefficient map. -/
@[simp] theorem evaluateAt_one (n : ℕ) [NeZero n] (f : Elem A n) :
    evaluateAt n (1 : S) (one_pow n) f = algebraMap A S (augmentation n f) := by
  simp [evaluateAt_apply, augmentation_apply, map_sum]

/-- Naturality under an algebra homomorphism that sends the chosen root to the
chosen target root.  Both root equations remain explicit proved hypotheses. -/
theorem map_evaluateAt_hom (n : ℕ) [NeZero n]
    (x : S) (hx : x ^ n = 1) (y : T) (hy : y ^ n = 1)
    (ψ : S →ₐ[A] T) (hxy : ψ x = y) :
    ψ.comp (evaluateAt n x hx) = evaluateAt n y hy := by
  apply AddMonoidAlgebra.algHom_ext
  · intro a
    simp [AlgHom.comp_apply, evaluateAt_single, hxy]
  · exact Subsingleton.elim _ _

theorem map_evaluateAt (n : ℕ) [NeZero n]
    (x : S) (hx : x ^ n = 1) (y : T) (hy : y ^ n = 1)
    (ψ : S →ₐ[A] T) (hxy : ψ x = y) (f : Elem A n) :
    ψ (evaluateAt n x hx f) = evaluateAt n y hy f :=
  DFunLike.congr_fun (map_evaluateAt_hom n x hx y hy ψ hxy) f

/-- In particular, a residue map sending the root to one sends evaluation to
the residue of augmentation. -/
theorem map_evaluateAt_of_map_eq_one (n : ℕ) [NeZero n]
    (x : S) (hx : x ^ n = 1) (ψ : S →ₐ[A] T) (hx1 : ψ x = 1) (f : Elem A n) :
    ψ (evaluateAt n x hx f) = algebraMap A T (augmentation n f) := by
  rw [map_evaluateAt n x hx 1 (one_pow n) ψ hx1, evaluateAt_one]

end CirculantHadamard.CyclicRing

end

end OAI
