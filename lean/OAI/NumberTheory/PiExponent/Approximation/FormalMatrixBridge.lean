import OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation
import OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap
import OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap

namespace OAI

noncomputable section

namespace PiExponent.FormalMatrixBridge

open MvPowerSeries
open scoped BigOperators

def flatten (m : ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp
    ((MvPolynomial.finSuccEquiv ℂ m).symm.toAlgHom.comp
      (nestedPolynomialSwap ℂ m).toAlgHom)

@[simp] theorem coeff_flatten {m : ℕ}
    (p : MvPolynomial (Fin m) (Polynomial ℂ)) (d : Fin (m+1) →₀ ℕ) :
    coeff d (flatten m p) = (p.coeff d.tail).coeff (d 0) := by
  change ((MvPolynomial.finSuccEquiv ℂ m).symm (nestedPolynomialSwap ℂ m p)).coeff d = _
  rw [← Finsupp.cons_tail d, ← MvPolynomial.finSuccEquiv_coeff_coeff,
    AlgEquiv.apply_symm_apply]
  exact coeff_nestedPolynomialSwap p (d 0) d.tail

@[simp] theorem flatten_C {m : ℕ} (p : Polynomial ℂ) :
    flatten m (MvPolynomial.C p) = FormalLogJet.liftSeries m (p : PowerSeries ℂ) := by
  classical
  ext d
  rw [coeff_flatten, FormalLogJet.coeff_liftSeries]
  simp only [MvPolynomial.coeff_C, Polynomial.coeff_coe]
  split_ifs <;> simp_all

@[simp] theorem flatten_X {m : ℕ} (i : Fin m) :
    flatten m (MvPolynomial.X i) = X i.succ := by
  classical
  ext d
  rw [coeff_flatten, MvPolynomial.coeff_X, coeff_X]
  have hd : d = Finsupp.single i.succ 1 ↔
      d.tail = Finsupp.single i 1 ∧ d 0 = 0 := by
    conv_lhs => rw [← Finsupp.cons_tail d]
    exact Finsupp.cons_eq_single_succ_iff i
  simp only [hd]
  by_cases ht : Finsupp.single i 1 = d.tail
  · rw [ite_eq_left ht]
    have ht' : d.tail = Finsupp.single i 1 := ht.symm
    simp only [ht', true_and, Polynomial.coeff_one]
  · rw [ite_eq_right ht, Polynomial.coeff_zero]
    have ht' : ¬ d.tail = Finsupp.single i 1 := Ne.symm ht
    simp only [ht', false_and, ite_false]

theorem flatten_literalJetSubstitution {m : ℕ}
    (r : Fin m → ℂ) (T : Fin m → ℕ) (j : ℕ)
    (p : PiExponentApprox.FramePolynomial m) :
    flatten m (literalJetSubstitution r
      (fun i => InterpolationMatrix.truncatedLog (T i)) j p) =
      FormalLogTruncation.truncatedFormalJet (fun i => (j : ℂ) * r i) T p := by
  have hh : (flatten m).comp
      (literalJetSubstitution r (fun i => InterpolationMatrix.truncatedLog (T i)) j) =
        FormalLogTruncation.truncatedFormalJet (fun i => (j : ℂ) * r i) T := by
    ext i
    cases i using Fin.cases with
    | zero =>
      simp [literalJetSubstitution, FormalLogTruncation.truncatedFormalJet]
    | succ i =>
      simp [literalJetSubstitution, FormalLogTruncation.truncatedFormalJet,
        InterpolationMatrix.truncatedLog, add_assoc, add_left_comm, add_comm]
  exact DFunLike.congr_fun hh p

theorem coeff_truncatedFormalJet {m : ℕ}
    (r : Fin m → ℂ) (T : Fin m → ℕ) (j : ℕ)
    (p : PiExponentApprox.FramePolynomial m) (d : Fin (m+1) →₀ ℕ) :
    coeff d (FormalLogTruncation.truncatedFormalJet
      (fun i => (j : ℂ) * r i) T p) =
      ((literalJetSubstitution r (fun i => InterpolationMatrix.truncatedLog (T i)) j p).coeff
        d.tail).coeff (d 0) := by
  rw [← flatten_literalJetSubstitution, coeff_flatten]

@[simp] theorem exponentVector_tail {m : ℕ} (a : Fin (m+1) → ℕ) :
    (InterpolationMatrix.exponentVector a).tail =
      InterpolationMatrix.exponentVector (fun i => a i.succ) := by
  ext i
  simp [Finsupp.tail_apply]

theorem entry_eq_coeff_truncatedFormalJet {m : ℕ}
    (r : Fin m → ℂ) (T : Fin m → ℕ) (j : ℕ)
    (b e : Fin (m+1) → ℕ) :
    InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i))
      j (b 0) (fun i => b i.succ) (e 0) (fun i => e i.succ) =
      coeff (InterpolationMatrix.exponentVector b)
        (FormalLogTruncation.truncatedFormalJet (fun i => (j : ℂ) * r i) T
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) 1)) := by
  rw [coeff_truncatedFormalJet, literalJetSubstitution_monomial]
  simp [InterpolationMatrix.entry]

theorem truncatedLogMatrix_mulVec_eq_coeff {m : ℕ}
    (K : ℕ) (w0 v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ)
    (x : InterpolationMatrix.Column w0 w H → ℂ)
    (ρ : InterpolationMatrix.Row K v0 θ w H) :
    (InterpolationMatrix.truncatedLogMatrix K w0 v0 θ w H r T).mulVecLin x ρ =
      coeff (InterpolationMatrix.exponentVector ρ.2.val)
        (FormalLogTruncation.truncatedFormalJet (fun i => (ρ.1.val : ℂ) * r i) T
          (polynomialOfCoefficients
            (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) H) x)) := by
  rw [coeff_truncatedFormalJet, literalJetSubstitution_polynomialOfCoefficients]
  simpa only [exponentVector_tail, InterpolationMatrix.exponentVector_apply,
    InterpolationMatrix.linearEvaluation, InterpolationMatrix.truncatedLogMatrix] using
    InterpolationMatrix.linearEvaluation_eq_coeff K w0 v0 θ w H r
      (fun i => InterpolationMatrix.truncatedLog (T i)) x ρ

end PiExponent.FormalMatrixBridge

end

end OAI
