import OAI.Analysis.KadisonKastler.ClosedExpectation
import OAI.Analysis.KadisonKastler.RecoveryJointLaw
import OAI.Analysis.KadisonKastler.AffineExpectationAverage

namespace OAI

/-! # The affine expectation of the scalar recovery observable -/

namespace KadisonKastler

noncomputable section

universe u v

variable {B : Type u} [CStarAlgebra B]

/-- The expression averaged over the finite random choices in the scalar
recovery argument. -/
def recoveryObservable (n N : ℕ) (p : B) (u : unitary B) : B :=
  (n : ℂ) • (unitaryHaarPolynomial N u *
    recoveryContraction n p (unitaryHaarPolynomial N u) * unitaryHaarPolynomial N u)

theorem norm_recoveryObservable_le {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (p : B) (u : unitary B) : ‖recoveryObservable n N p u‖ ≤ (n : ℝ) * N := by
  let f := unitaryHaarPolynomial N u
  let c := recoveryContraction n p f
  have hf : ‖f‖ ≤ Real.sqrt (N : ℝ) := norm_unitaryHaarPolynomial_le_sqrt u hN
  have hc : ‖c‖ ≤ 1 := recoveryContraction_norm_le hn p f
  have hprod : ‖f * c * f‖ ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := by
    calc
      ‖f * c * f‖ ≤ (‖f‖ * ‖c‖) * ‖f‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (Real.sqrt (N : ℝ) * 1) * Real.sqrt (N : ℝ) :=
        mul_le_mul (mul_le_mul hf hc (norm_nonneg _) (Real.sqrt_nonneg _)) hf
          (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) zero_le_one)
      _ = _ := by rw [mul_one]
  change ‖(n : ℂ) • (f * c * f)‖ ≤ _
  rw [norm_smul, Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg n)).trans_eq
    (by rw [Real.mul_self_sqrt (Nat.cast_nonneg N)])

theorem recoveryObservable_mem_projectionHaarClosedAlgebra
    (n N : ℕ) (p : B) (u : unitary B) :
    recoveryObservable n N p u ∈ projectionHaarClosedAlgebra p u :=
  (projectionHaarClosedAlgebra p u).smul_mem
    (recoveryExpression_mem_projectionHaarClosedAlgebra n N p u) _

theorem FreeHaarMoments.recoveryExpectation_affine
    {τ : FaithfulTracialState B} {A : StarSubalgebra ℂ B} {u : unitary B}
    (h : FreeHaarMoments τ A u)
    (E : B →L[ℂ] B) (hE : ∀ x, E x ∈ A)
    (hpair : ∀ b ∈ A, ∀ x, τ.toLinearMap (b * E x) = τ.toLinearMap (b * x))
    {p : B} (hp : IsStarProjection p) (hpA : p ∈ A) (n N : ℕ) :
    ∃ α β : ℂ, E (recoveryObservable n N p u) = α • p + β • (1 : B) := by
  apply h.expectation_eq_affine_projection_of_mem_closure E hE hpair hp hpA
  rw [← projectionHaarClosedAlgebra_coe p hp u]
  exact recoveryObservable_mem_projectionHaarClosedAlgebra n N p u

variable {C : Type v} [CStarAlgebra C]

/-- The two determining trace values of the recovery observable are
independent of the free pair, with the projection trace fixed. -/
theorem freeHaar_recoveryObservable_pairings_eq
    (τ : FaithfulTracialState B) (σ : FaithfulTracialState C)
    {A : StarSubalgebra ℂ B} {D : StarSubalgebra ℂ C}
    {u : unitary B} {v : unitary C}
    (hu : FreeHaarMoments τ A u) (hv : FreeHaarMoments σ D v)
    {p : B} {q : C} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpA : p ∈ A) (hqD : q ∈ D) {t : ℂ}
    (hpτ : τ.toLinearMap p = t) (hqσ : σ.toLinearMap q = t)
    {n : ℕ} (hn : 0 < n) (N : ℕ) :
    τ.toLinearMap (recoveryObservable n N p u) =
      σ.toLinearMap (recoveryObservable n N q v) ∧
    τ.toLinearMap (p * recoveryObservable n N p u) =
      σ.toLinearMap (q * recoveryObservable n N q v) := by
  obtain ⟨htrace, hptrace⟩ :=
    freeHaar_recovery_pairings_eq τ σ hu hv hp hq hpA hqD hpτ hqσ hn N
  constructor
  · simpa only [recoveryObservable, map_smul] using congrArg ((n : ℂ) • ·) htrace
  · simpa only [recoveryObservable, mul_smul_comm, map_smul] using
      congrArg ((n : ℂ) • ·) hptrace

/-- The actual recovery observables have scalar averaged expectation.
The averaging premise refers only to the finite family of projections. -/
theorem finiteAverage_recoveryExpectation
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (τ : FaithfulTracialState B) (A : StarSubalgebra ℂ B)
    (E : B →L[ℂ] B) (hE : ∀ x, E x ∈ A)
    (hpair : ∀ b ∈ A, ∀ x, τ.toLinearMap (b * E x) = τ.toLinearMap (b * x))
    (p : ι → B) (u : ι → unitary B)
    (hp : ∀ i, IsStarProjection (p i)) (hpA : ∀ i, p i ∈ A)
    (hfree : ∀ i, FreeHaarMoments τ A (u i)) {t : ℂ}
    (hptrace : ∀ i, τ.toLinearMap (p i) = t) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hpavg : finiteAverage p = t • (1 : B))
    {n : ℕ} (hn : 0 < n) (N : ℕ) (i₀ : ι) :
    finiteAverage (fun i => E (recoveryObservable n N (p i) (u i))) =
      τ.toLinearMap (recoveryObservable n N (p i₀) (u i₀)) • (1 : B) := by
  apply finiteAverage_affine_projections τ p _ hp hptrace ht0 ht1 hpavg
  · intro i
    exact (hfree i).recoveryExpectation_affine E hE hpair (hp i) (hpA i) n N
  · intro i
    have hEi := hpair 1 A.one_mem (recoveryObservable n N (p i) (u i))
    simp only [one_mul] at hEi
    exact hEi.trans
      (freeHaar_recoveryObservable_pairings_eq τ τ (hfree i) (hfree i₀)
        (hp i) (hp i₀) (hpA i) (hpA i₀) (hptrace i) (hptrace i₀) hn N).1
  · intro i
    exact (hpair (p i) (hpA i) (recoveryObservable n N (p i) (u i))).trans
      (freeHaar_recoveryObservable_pairings_eq τ τ (hfree i) (hfree i₀)
        (hp i) (hp i₀) (hpA i) (hpA i₀) (hptrace i) (hptrace i₀) hn N).2

theorem expectation_finiteAverage_recoveryObservable
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (τ : FaithfulTracialState B) (A : StarSubalgebra ℂ B)
    (E : B →L[ℂ] B) (hE : ∀ x, E x ∈ A)
    (hpair : ∀ b ∈ A, ∀ x, τ.toLinearMap (b * E x) = τ.toLinearMap (b * x))
    (p : ι → B) (u : ι → unitary B)
    (hp : ∀ i, IsStarProjection (p i)) (hpA : ∀ i, p i ∈ A)
    (hfree : ∀ i, FreeHaarMoments τ A (u i)) {t : ℂ}
    (hptrace : ∀ i, τ.toLinearMap (p i) = t) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hpavg : finiteAverage p = t • (1 : B))
    {n : ℕ} (hn : 0 < n) (N : ℕ) (i₀ : ι) :
    E (finiteAverage (fun i => recoveryObservable n N (p i) (u i))) =
      τ.toLinearMap (recoveryObservable n N (p i₀) (u i₀)) • (1 : B) := by
  rw [show E (finiteAverage (fun i => recoveryObservable n N (p i) (u i))) =
      finiteAverage (fun i => E (recoveryObservable n N (p i) (u i))) by
    simp only [finiteAverage, map_smul, map_sum]]
  exact finiteAverage_recoveryExpectation τ A E hE hpair p u hp hpA hfree
    hptrace ht0 ht1 hpavg hn N i₀

end

end KadisonKastler

end OAI
