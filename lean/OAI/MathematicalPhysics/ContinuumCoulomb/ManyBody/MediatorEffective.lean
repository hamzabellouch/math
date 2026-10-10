import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorCompression
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePauli
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace OAI

/-! Exact effective matrices for simultaneous singlet mediators, on the
complete original-spin Hilbert space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker

abbrev MediatedSpinBasis (n r : ℕ) := SourceSpinBasis n × MediatorBasis r

/-- Restriction to original spins tensored with all mediator singlets. -/
def mediatorCompression (n r : ℕ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ →ₗ[ℂ]
      Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ where
  toFun M s t := M (s, mediatorVacuum r) (t, mediatorVacuum r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mediatorCompression_kronecker (n r : ℕ)
    (A : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (M : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) :
    mediatorCompression n r (A ⊗ₖ M) =
      M (mediatorVacuum r) (mediatorVacuum r) • A := by
  ext s t
  change A s t * M (mediatorVacuum r) (mediatorVacuum r) =
    M (mediatorVacuum r) (mediatorVacuum r) * A s t
  ring

def liftedMediatorInverse (n r : ℕ) (Delta : ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  1 ⊗ₖ mediatorInverseMatrix r Delta

def elementaryMediatorSpoke (n r : ℕ) (e : Fin r) (member : Fin 2) (μ : Fin 3)
    (A : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  A ⊗ₖ mediatorLocal r e (bellMemberPauli member μ)

/-- Fresh-pair cancellation with arbitrary original-spin operators.
This is a matrix identity and therefore covers entangled original states. -/
theorem elementaryMediatorSpoke_compression (n r : ℕ) (Delta : ℝ) (e f : Fin r)
    (member other : Fin 2) (μ ν : Fin 3)
    (A B : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    mediatorCompression n r
      (elementaryMediatorSpoke n r e member μ A * liftedMediatorInverse n r Delta *
        elementaryMediatorSpoke n r f other ν B) =
      if e = f ∧ μ = ν then
        (((4 * Delta)⁻¹ : ℝ) * (if member = other then (1 : ℂ) else -1)) • (A * B)
      else 0 := by
  unfold elementaryMediatorSpoke liftedMediatorInverse
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one,
    mediatorCompression_kronecker, mediator_pauli_inverse_compression]
  split_ifs <;> simp

/-- The two physical spokes incident to one original edge. The left spoke
uses the first mediator member; the right can use either member. -/
def mediatorEdgeSpoke (n r : ℕ) (e : Fin r) (i j : Fin n) (member : Fin 2) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ μ : Fin 3,
    (elementaryMediatorSpoke n r e 0 μ (sourceLocalPauli n i μ) +
      elementaryMediatorSpoke n r e member μ (sourceLocalPauli n j μ))

theorem mediatorEdgeSpoke_cross_compression (n r : ℕ) (Delta : ℝ)
    (e f : Fin r) (hef : e ≠ f) (i j k l : Fin n) (member other : Fin 2) :
    mediatorCompression n r
      (mediatorEdgeSpoke n r e i j member * liftedMediatorInverse n r Delta *
        mediatorEdgeSpoke n r f k l other) = 0 := by
  unfold mediatorEdgeSpoke
  simp only [Finset.sum_mul, Finset.mul_sum, add_mul, mul_add, map_sum, map_add]
  simp_rw [elementaryMediatorSpoke_compression]
  simp [hef]


def mediatorAxisSpoke (n r : ℕ) (e : Fin r) (i : Fin n) (member : Fin 2) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ μ : Fin 3, elementaryMediatorSpoke n r e member μ (sourceLocalPauli n i μ)

theorem mediatorAxisSpoke_compression (n r : ℕ) (Delta : ℝ) (e f : Fin r)
    (i j : Fin n) (member other : Fin 2) :
    mediatorCompression n r
      (mediatorAxisSpoke n r e i member * liftedMediatorInverse n r Delta *
        mediatorAxisSpoke n r f j other) =
      if e = f then
        (((4 * Delta)⁻¹ : ℝ) * (if member = other then (1 : ℂ) else -1)) •
          ∑ μ : Fin 3, sourceLocalPauli n i μ * sourceLocalPauli n j μ
      else 0 := by
  classical
  unfold mediatorAxisSpoke
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
  simp_rw [elementaryMediatorSpoke_compression]
  by_cases hef : e = f
  · subst f
    simp [Finset.smul_sum]
  · simp [hef]

theorem mediatorEdgeSpoke_as_add (n r : ℕ) (e : Fin r) (i j : Fin n) (member : Fin 2) :
    mediatorEdgeSpoke n r e i j member =
      mediatorAxisSpoke n r e i 0 + mediatorAxisSpoke n r e j member := by
  unfold mediatorEdgeSpoke mediatorAxisSpoke
  rw [Finset.sum_add_distrib]

def mediatorMemberSign (member : Fin 2) : ℂ := if member = 0 then 1 else -1

/-- Exact two-spoke self-energy, including the scalar shift six/(four Delta). -/
theorem mediatorEdgeSpoke_self_compression (n r : ℕ) (Delta : ℝ) (e : Fin r)
    (i j : Fin n) (hij : i ≠ j) (member : Fin 2) :
    mediatorCompression n r
      (mediatorEdgeSpoke n r e i j member * liftedMediatorInverse n r Delta *
        mediatorEdgeSpoke n r e i j member) =
      (((4 * Delta)⁻¹ : ℝ) : ℂ) •
        ((6 : ℂ) • 1 + (2 * mediatorMemberSign member) • sourceHeisenbergMatrix n i j) := by
  classical
  simp only [mediatorEdgeSpoke_as_add]
  simp only [add_mul, mul_add, map_add, mediatorAxisSpoke_compression, ite_true]
  have hsquare (k : Fin n) :
      (∑ μ : Fin 3, sourceLocalPauli n k μ * sourceLocalPauli n k μ) = (3 : ℂ) • 1 := by
    simp_rw [sourceLocalPauli_sq]
    ext s t
    norm_num [Matrix.sum_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have hreverse : (∑ μ : Fin 3, sourceLocalPauli n j μ * sourceLocalPauli n i μ) =
      sourceHeisenbergMatrix n i j := by
    rw [← sourceLocalPauli_sum n i j hij]
    apply Finset.sum_congr rfl
    intro μ _
    exact sourceLocalPauli_commute n j i hij.symm μ μ
  rw [hsquare i, hsquare j, sourceLocalPauli_sum n i j hij, hreverse]
  have hsign : (if (0 : Fin 2) = member then (1 : ℂ) else -1) = mediatorMemberSign member := by
    simp only [mediatorMemberSign, eq_comm]
  simp only [hsign, mediatorMemberSign, mul_one]
  ext s t
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem mediatorEdgeSpoke_compression (n r : ℕ) (Delta : ℝ) (e f : Fin r)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e) (member : Fin r → Fin 2) :
    mediatorCompression n r
      (mediatorEdgeSpoke n r e (left e) (right e) (member e) *
        liftedMediatorInverse n r Delta *
        mediatorEdgeSpoke n r f (left f) (right f) (member f)) =
      if e = f then
        (((4 * Delta)⁻¹ : ℝ) : ℂ) • ((6 : ℂ) • 1 +
          (2 * mediatorMemberSign (member e)) • sourceHeisenbergMatrix n (left e) (right e))
      else 0 := by
  classical
  by_cases hef : e = f
  · subst f
    simp only [ite_true]
    exact mediatorEdgeSpoke_self_compression n r Delta e _ _ (hneq e) _
  · rw [ite_eq_right hef]
    exact mediatorEdgeSpoke_cross_compression n r Delta e f hef _ _ _ _ _ _

def totalMediatorSpokes (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ e, (amplitude e : ℂ) • mediatorEdgeSpoke n r e (left e) (right e) (member e)

/-- The simultaneous second-order matrix contains no cross-edge terms. -/
theorem totalMediatorSpokes_compression (n r : ℕ) (Delta : ℝ)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    mediatorCompression n r
      (totalMediatorSpokes n r left right member amplitude * liftedMediatorInverse n r Delta *
        totalMediatorSpokes n r left right member amplitude) =
      ∑ e, ((amplitude e : ℂ) ^ 2 * ((4 * Delta)⁻¹ : ℝ)) •
        ((6 : ℂ) • 1 + (2 * mediatorMemberSign (member e)) •
          sourceHeisenbergMatrix n (left e) (right e)) := by
  classical
  unfold totalMediatorSpokes
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_sum, map_smul]
  simp_rw [mediatorEdgeSpoke_compression n r Delta _ _ left right hneq member]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_smul]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  ring

def signedMediatorMember (J : ℝ) : Fin 2 := if J < 0 then 0 else 1

def signedMediatorAmplitude (Delta J : ℝ) : ℝ := Real.sqrt (2 * Delta * |J|)

theorem signedMediatorAmplitude_nonneg (Delta J : ℝ) :
    0 ≤ signedMediatorAmplitude Delta J := Real.sqrt_nonneg _

theorem signedMediatorAmplitude_calibration {Delta : ℝ} (hDelta : 0 ≤ Delta) (J : ℝ) :
    signedMediatorAmplitude Delta J ^ 2 = 2 * Delta * |J| := by
  unfold signedMediatorAmplitude
  exact Real.sq_sqrt (by positivity)

/-- The exact manuscript calibration, with the constant self-energy retained. -/
theorem calibratedMediator_edge {Delta amplitude J : ℝ} (hDelta : 0 < Delta)
    (hcal : amplitude ^ 2 = 2 * Delta * |J|)
    {n : ℕ} (i j : Fin n) :
    ((amplitude : ℂ) ^ 2 * ((4 * Delta)⁻¹ : ℝ)) •
      ((6 : ℂ) • 1 + (2 * mediatorMemberSign (signedMediatorMember J)) •
        sourceHeisenbergMatrix n i j) =
      (3 * |J| : ℝ) • (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) -
        (J : ℂ) • sourceHeisenbergMatrix n i j := by
  have hratioReal : amplitude ^ 2 * (4 * Delta)⁻¹ = |J| / 2 := by
    rw [hcal]
    field_simp [ne_of_gt hDelta]
    ring
  have hratio : (amplitude : ℂ) ^ 2 * ((4 * Delta)⁻¹ : ℝ) = (|J| / 2 : ℝ) := by
    exact_mod_cast hratioReal
  rw [hratio, smul_add, smul_smul, smul_smul]
  have hconstant : ((|J| / 2 : ℝ) : ℂ) * 6 = ((3 * |J| : ℝ) : ℂ) := by
    push_cast
    ring
  have hcoupling : ((|J| / 2 : ℝ) : ℂ) *
      (2 * mediatorMemberSign (signedMediatorMember J)) = -(J : ℂ) := by
    by_cases hJ : J < 0
    · simp only [signedMediatorMember, ite_eq_left hJ, mediatorMemberSign, ite_true,
        abs_of_neg hJ]
      push_cast
      ring
    · have hJpos : 0 ≤ J := le_of_not_gt hJ
      norm_num only [signedMediatorMember, ite_eq_right hJ, mediatorMemberSign,
        show (1 : Fin 2) ≠ 0 by decide, ite_false, abs_of_nonneg hJpos]
      push_cast
      ring
  rw [hconstant, hcoupling, neg_smul, sub_eq_add_neg]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- Exact signed-source simulation at second order for all original-spin
states. Unreplaced terms survive as the explicit low block C. -/
theorem signedMediator_effective_matrix (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J amplitude : Fin r → ℝ) (hcal : ∀ e, amplitude e ^ 2 = 2 * Delta * |J e|)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    C - mediatorCompression n r
      (totalMediatorSpokes n r left right (fun e => signedMediatorMember (J e)) amplitude *
        liftedMediatorInverse n r Delta *
        totalMediatorSpokes n r left right (fun e => signedMediatorMember (J e)) amplitude) =
      C + (∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e)) -
        (3 * ∑ e, |J e| : ℝ) • 1 := by
  rw [totalMediatorSpokes_compression n r Delta left right hneq]
  simp_rw [calibratedMediator_edge hDelta (hcal _) ]
  rw [Finset.sum_sub_distrib]
  have hconstant : (∑ e, (3 * |J e| : ℝ) •
      (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)) =
      (3 * ∑ e, |J e| : ℝ) • 1 := by
    rw [← Finset.sum_smul, Finset.mul_sum]
  rw [hconstant]
  abel


def physicalMemberPauli (member : Fin 2) (μ : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  if member = 0 then firstPauli μ else secondPauli μ

theorem physicalMemberPauli_transform (member : Fin 2) (μ : Fin 3) :
    bellTransform (physicalMemberPauli member μ) = bellMemberPauli member μ := by
  unfold physicalMemberPauli bellMemberPauli
  split_ifs <;> rfl

def fullMediatorBellMatrix (n r : ℕ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  1 ⊗ₖ globalBellMatrix r

theorem fullMediatorBellMatrix_gram (n r : ℕ) :
    (fullMediatorBellMatrix n r).conjTranspose * fullMediatorBellMatrix n r = 1 := by
  unfold fullMediatorBellMatrix
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, one_mul, globalBellMatrix_gram,
    Matrix.one_kronecker_one]

theorem fullMediatorBellMatrix_cogram (n r : ℕ) :
    fullMediatorBellMatrix n r * (fullMediatorBellMatrix n r).conjTranspose = 1 := by
  unfold fullMediatorBellMatrix
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, one_mul, globalBellMatrix_cogram,
    Matrix.one_kronecker_one]

/-- The elementary matrices above are precisely Bell transforms of the
physical original-spin to mediator-member Pauli interactions. -/
theorem physicalSpoke_bellTransform (n r : ℕ) (e : Fin r) (member : Fin 2) (μ : Fin 3)
    (A : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      (A ⊗ₖ mediatorLocal r e (physicalMemberPauli member μ)) * fullMediatorBellMatrix n r =
      elementaryMediatorSpoke n r e member μ A := by
  unfold fullMediatorBellMatrix elementaryMediatorSpoke
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, one_mul, mul_one, mediatorLocal_bellTransform,
    physicalMemberPauli_transform]


theorem elementaryMediatorSpoke_low_compression (n r : ℕ) (e : Fin r)
    (member : Fin 2) (μ : Fin 3)
    (A : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    mediatorCompression n r (elementaryMediatorSpoke n r e member μ A) = 0 := by
  unfold elementaryMediatorSpoke
  rw [mediatorCompression_kronecker, mediatorLocal_vacuum, bellMemberPauli_zero, zero_smul]

theorem totalMediatorSpokes_low_compression (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    mediatorCompression n r (totalMediatorSpokes n r left right member amplitude) = 0 := by
  unfold totalMediatorSpokes mediatorEdgeSpoke
  simp only [map_sum, map_smul, map_add, elementaryMediatorSpoke_low_compression,
    add_zero, smul_zero, Finset.sum_const_zero]

/-- The unreplaced original Hamiltonian survives the low compression exactly. -/
theorem mediator_first_order_matrix (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    mediatorCompression n r
      (C ⊗ₖ 1 + totalMediatorSpokes n r left right member amplitude) = C := by
  rw [map_add, mediatorCompression_kronecker, totalMediatorSpokes_low_compression]
  simp

end ContinuumCoulomb

end

end OAI
