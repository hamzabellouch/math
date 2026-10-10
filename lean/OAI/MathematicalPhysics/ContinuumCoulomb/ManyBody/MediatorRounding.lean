import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorOffsets

namespace OAI

/-! Full finite-spin spectral stability under rational approximation of the
physical mediator spokes. The infimum ranges over all entangled states. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem mediatorRayleigh_abs_le (n r : ℕ)
    (H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (x : MediatorFullSpace n r) :
    |⟪x, spinMatrixOperator H x⟫_ℝ| ≤ ‖spinMatrixOperator H‖ * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖x‖ * ‖spinMatrixOperator H x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖spinMatrixOperator H‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((spinMatrixOperator H).le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

theorem mediatorRayleigh_boundedBelow (n r : ℕ)
    (H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    BddBelow {e | ∃ x : MediatorFullSpace n r, 0 < ‖x‖ ^ 2 ∧
      e = ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2} := by
  refine ⟨-‖spinMatrixOperator H‖, ?_⟩
  rintro e ⟨x, hx, rfl⟩
  apply (le_div_iff₀ hx).mpr
  have h := (abs_le.mp (mediatorRayleigh_abs_le n r H x)).1
  nlinarith

theorem mediatorRayleigh_nonempty (n r : ℕ)
    (H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    {e | ∃ x : MediatorFullSpace n r, 0 < ‖x‖ ^ 2 ∧
      e = ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2}.Nonempty := by
  let x : MediatorFullSpace n r := EuclideanSpace.single ((fun _ => 0), mediatorVacuum r) 1
  exact ⟨_, x, by simp [x], rfl⟩

theorem mediatorRayleigh_difference (n r : ℕ)
    (H K : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (x : MediatorFullSpace n r) (hx : 0 < ‖x‖ ^ 2) :
    |⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2 -
      ⟪x, spinMatrixOperator K x⟫_ℝ / ‖x‖ ^ 2| ≤ ‖spinMatrixOperator (H - K)‖ := by
  rw [← sub_div, ← inner_sub_right, ← _root_.sub_apply, ← spinMatrixOperator_sub,
    abs_div, abs_of_pos hx]
  exact (div_le_iff₀ hx).mpr (mediatorRayleigh_abs_le n r (H - K) x)

theorem mediatorFullBottom_lipschitz (n r : ℕ)
    (H K : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    |mediatorFullBottom n r H - mediatorFullBottom n r K| ≤ ‖spinMatrixOperator (H - K)‖ := by
  have hbound : mediatorFullBottom n r K - ‖spinMatrixOperator (H - K)‖ ≤
      mediatorFullBottom n r H := by
    apply le_csInf (mediatorRayleigh_nonempty n r H)
    rintro e ⟨x, hx, rfl⟩
    have htrial : mediatorFullBottom n r K ≤ ⟪x, spinMatrixOperator K x⟫_ℝ / ‖x‖ ^ 2 :=
      csInf_le (mediatorRayleigh_boundedBelow n r K) ⟨x, hx, rfl⟩
    have h := (abs_le.mp (mediatorRayleigh_difference n r H K x hx)).1
    linarith
  have hbound' : mediatorFullBottom n r H - ‖spinMatrixOperator (H - K)‖ ≤
      mediatorFullBottom n r K := by
    apply le_csInf (mediatorRayleigh_nonempty n r K)
    rintro e ⟨x, hx, rfl⟩
    have htrial : mediatorFullBottom n r H ≤ ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2 :=
      csInf_le (mediatorRayleigh_boundedBelow n r H) ⟨x, hx, rfl⟩
    have h := (abs_le.mp (mediatorRayleigh_difference n r H K x hx)).2
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem spinMatrixOperator_conjugate_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U M : Matrix ι ι ℂ) (hGram : U.conjTranspose * U = 1)
    (hCogram : U * U.conjTranspose = 1) :
    ‖spinMatrixOperator (U * M * U.conjTranspose)‖ ≤ ‖spinMatrixOperator M‖ := by
  have hU := spinMatrixOperator_unitary_norm U hGram
  have hUs := spinMatrixOperator_unitary_norm U.conjTranspose
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hCogram)
  rw [spinMatrixOperator_mul, spinMatrixOperator_mul]
  calc
    _ ≤ ‖spinMatrixOperator U‖ * ‖spinMatrixOperator M‖ *
        ‖spinMatrixOperator U.conjTranspose‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖spinMatrixOperator M‖ * 1 := by gcongr
    _ = _ := by ring

theorem physicalMediatorEdgeSpoke_operator_norm (n r : ℕ) (e : Fin r)
    (i j : Fin n) (member : Fin 2) :
    ‖spinMatrixOperator (physicalMediatorEdgeSpoke n r e i j member)‖ ≤ 6 := by
  let U := fullMediatorBellMatrix n r
  have hGram : U.conjTranspose * U = 1 := fullMediatorBellMatrix_gram n r
  have hCogram : U * U.conjTranspose = 1 := fullMediatorBellMatrix_cogram n r
  have hback : U * mediatorEdgeSpoke n r e i j member * U.conjTranspose =
      physicalMediatorEdgeSpoke n r e i j member := by
    rw [← physicalMediatorEdgeSpoke_transform]
    change U * (U.conjTranspose * physicalMediatorEdgeSpoke n r e i j member * U) * U.conjTranspose = _
    calc
      _ = (U * U.conjTranspose) * physicalMediatorEdgeSpoke n r e i j member *
          (U * U.conjTranspose) := by noncomm_ring
      _ = _ := by rw [hCogram]; simp
  rw [← hback]
  exact (spinMatrixOperator_conjugate_norm_le U _ hGram hCogram).trans
    (mediatorEdgeSpoke_operator_norm n r e i j member)

theorem physicalTotalMediatorSpokes_operator_norm (n r : ℕ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    ‖spinMatrixOperator (physicalTotalMediatorSpokes n r left right member amplitude)‖ ≤
      6 * ∑ e, |amplitude e| := by
  unfold physicalTotalMediatorSpokes
  rw [spinMatrixOperator_sum]
  simp only [spinMatrixOperator_smul]
  calc
    _ ≤ ∑ e, ‖(amplitude e : ℂ) • spinMatrixOperator
        (physicalMediatorEdgeSpoke n r e (left e) (right e) (member e))‖ := norm_sum_le _ _
    _ ≤ ∑ e, 6 * |amplitude e| := by
      apply Finset.sum_le_sum
      intro e _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (physicalMediatorEdgeSpoke_operator_norm n r e _ _ _)
        (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem physicalTotalMediatorSpokes_sub (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (a b : Fin r → ℝ) :
    physicalTotalMediatorSpokes n r left right member a -
      physicalTotalMediatorSpokes n r left right member b =
        physicalTotalMediatorSpokes n r left right member (fun e => a e - b e) := by
  unfold physicalTotalMediatorSpokes
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← sub_smul, Complex.ofReal_sub]

/-- The physical rounded Hamiltonian is compared on the entire tensor
space, without a restriction to the singlet kernel. -/
theorem physicalRawMediator_bottom_rounding (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (a b : Fin r → ℝ) :
    |mediatorFullBottom n r (physicalRawMediatorHamiltonian n r Delta C left right member a) -
      mediatorFullBottom n r (physicalRawMediatorHamiltonian n r Delta C left right member b)| ≤
        6 * ∑ e, |a e - b e| := by
  have hdiff : physicalRawMediatorHamiltonian n r Delta C left right member a -
      physicalRawMediatorHamiltonian n r Delta C left right member b =
        physicalTotalMediatorSpokes n r left right member (fun e => a e - b e) := by
    rw [← physicalTotalMediatorSpokes_sub]
    unfold physicalRawMediatorHamiltonian
    abel
  exact (mediatorFullBottom_lipschitz n r _ _).trans (by
    rw [hdiff]
    exact physicalTotalMediatorSpokes_operator_norm n r left right member _)

end ContinuumCoulomb

end

end OAI
