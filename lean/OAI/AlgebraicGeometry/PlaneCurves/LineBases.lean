import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import OAI.AlgebraicGeometry.PlaneCurves.LineGeometry

namespace OAI

/-!
# Polynomial coordinates and bases on a projective line
-/

section

noncomputable section
open Module
namespace Nagata.W01

variable {K : Type*} [Field K]
abbrev ProjectivePlaneVector (K : Type*) := Fin 3 → K

/-- Distinct projective points have linearly independent actual representatives. -/
theorem projective_representatives_pair_independent
    (p q : Projectivization K (ProjectivePlaneVector K)) (hpq : p ≠ q) :
    LinearIndependent K ![p.rep, q.rep] := by
  rw [linearIndependent_fin2]
  refine ⟨q.rep_nonzero, ?_⟩
  intro a ha
  apply hpq
  rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep q]
  exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨a, ha⟩

/-- Two distinct points on an actual projective line extend to a basis whose
third vector has linear-form value one. The first two representatives are unchanged. -/
theorem exists_projective_line_basis
    (L : ProjectivePlaneVector K →ₗ[K] K) (hL : L ≠ 0)
    (p q : Projectivization K (ProjectivePlaneVector K))
    (hpq : p ≠ q) (hp : L p.rep = 0) (hq : L q.rep = 0) :
    ∃ b : Basis (Fin 3) K (ProjectivePlaneVector K),
      b 0 = p.rep ∧ b 1 = q.rep ∧ L (b 2) = 1 := by
  classical
  obtain ⟨w, hw⟩ := Nagata.Workers.W14.nonzero_linearFunctional_surjective L hL 1
  have hspan : Submodule.span K (Set.range ![p.rep, q.rep]) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    fin_cases i <;> simpa [LinearMap.mem_ker] using (by assumption : L _ = 0)
  have hwspan : w ∉ Submodule.span K (Set.range ![p.rep, q.rep]) := by
    intro h
    have hz : L w = 0 := hspan h
    exact one_ne_zero (hw.symm.trans hz)
  have hli : LinearIndependent K (Fin.snoc ![p.rep, q.rep] w) :=
    linearIndependent_finSnoc.mpr
      ⟨projective_representatives_pair_independent p q hpq, hwspan⟩
  let b := basisOfPiSpaceOfLinearIndependent hli
  have hb : (b : Fin 3 → ProjectivePlaneVector K) = Fin.snoc ![p.rep, q.rep] w :=
    coe_basisOfPiSpaceOfLinearIndependent hli
  refine ⟨b, ?_, ?_, ?_⟩
  · change (b : Fin 3 → ProjectivePlaneVector K) 0 = _
    rw [hb]
    rfl
  · change (b : Fin 3 → ProjectivePlaneVector K) 1 = _
    rw [hb]
    rfl
  · change L ((b : Fin 3 → ProjectivePlaneVector K) 2) = _
    rw [hb]
    exact hw

/-- In an adapted actual basis, linear-form evaluation is exactly the third coordinate. -/
theorem adapted_basis_third_coordinate
    (L : ProjectivePlaneVector K →ₗ[K] K)
    (b : Basis (Fin 3) K (ProjectivePlaneVector K))
    (h0 : L (b 0) = 0) (h1 : L (b 1) = 0) (h2 : L (b 2) = 1)
    (v : ProjectivePlaneVector K) : b.repr v 2 = L v := by
  have h := congrArg L (b.sum_repr v)
  rw [Fin.sum_univ_three] at h
  simpa only [map_add, map_smul, h0, h1, h2, smul_eq_mul, mul_zero, mul_one, zero_add] using h

/-- The actual projective line is precisely the zero third-coordinate plane. -/
theorem adapted_basis_mem_line_iff
    (L : ProjectivePlaneVector K →ₗ[K] K)
    (b : Basis (Fin 3) K (ProjectivePlaneVector K))
    (h0 : L (b 0) = 0) (h1 : L (b 1) = 0) (h2 : L (b 2) = 1)
    (v : ProjectivePlaneVector K) : L v = 0 ↔ b.repr v 2 = 0 := by
  rw [adapted_basis_third_coordinate L b h0 h1 h2]

/-- Three distinct zeros of a nonzero projective linear form admit the exact
normalization needed for binary polynomial restriction, with neither coefficient zero. -/
theorem exists_three_projective_zeros_basis
    (L : ProjectivePlaneVector K →ₗ[K] K) (hL : L ≠ 0)
    (p₀ p₁ p₂ : Projectivization K (ProjectivePlaneVector K))
    (h01 : p₀ ≠ p₁) (h20 : p₂ ≠ p₀) (h21 : p₂ ≠ p₁)
    (h0 : L p₀.rep = 0) (h1 : L p₁.rep = 0) (h2 : L p₂.rep = 0) :
    ∃ (b : Basis (Fin 3) K (ProjectivePlaneVector K)) (a c : K),
      b 0 = p₀.rep ∧ b 1 = p₁.rep ∧ L (b 2) = 1 ∧
      a ≠ 0 ∧ c ≠ 0 ∧ p₂.rep = a • b 0 + c • b 1 := by
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_projective_line_basis L hL p₀ p₁ h01 h0 h1
  have hL0 : L (b 0) = 0 := hb0 ▸ h0
  have hL1 : L (b 1) = 0 := hb1 ▸ h1
  have hz : b.repr p₂.rep 2 = 0 := by
    rw [adapted_basis_third_coordinate L b hL0 hL1 hb2, h2]
  have hex : p₂.rep = (b.repr p₂.rep 0) • b 0 + (b.repr p₂.rep 1) • b 1 := by
    have he := (b.sum_repr p₂.rep).symm
    rw [Fin.sum_univ_three] at he
    simpa only [hz, zero_smul, add_zero] using he
  have ha : b.repr p₂.rep 0 ≠ 0 := by
    intro ha
    have he : (b.repr p₂.rep 1) • p₁.rep = p₂.rep := by
      simpa [ha, hb1] using hex.symm
    apply h21
    rw [← Projectivization.mk_rep p₂, ← Projectivization.mk_rep p₁]
    exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨_, he⟩
  have hc : b.repr p₂.rep 1 ≠ 0 := by
    intro hc
    have he : (b.repr p₂.rep 0) • p₀.rep = p₂.rep := by
      simpa [hc, hb0] using hex.symm
    apply h20
    rw [← Projectivization.mk_rep p₂, ← Projectivization.mk_rep p₀]
    exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨_, he⟩
  exact ⟨b, _, _, hb0, hb1, hb2, ha, hc, hex⟩

end Nagata.W01

end
end

section

noncomputable section
open Module MvPolynomial
open scoped BigOperators
namespace Nagata.W01

abbrev PlanePolynomial := MvPolynomial (Fin 3) ℂ
abbrev ComplexPlaneVector := Fin 3 → ℂ

/-- The jth coordinate linear polynomial of an actual linear map. -/
def linearCoordinate (T : ComplexPlaneVector →ₗ[ℂ] ComplexPlaneVector) (j : Fin 3) :
    PlanePolynomial := ∑ i : Fin 3, C (T (Pi.single i 1) j) * X i

/-- Literal substitution of the three coordinate linear forms. -/
def linearSubstitution (T : ComplexPlaneVector →ₗ[ℂ] ComplexPlaneVector) :
    PlanePolynomial →ₐ[ℂ] PlanePolynomial := aeval (linearCoordinate T)

@[simp] theorem linearSubstitution_X
    (T : ComplexPlaneVector →ₗ[ℂ] ComplexPlaneVector) (j : Fin 3) :
    linearSubstitution T (X j) = linearCoordinate T j := aeval_X _ _

/-- Evaluation of a coordinate polynomial is the corresponding coordinate of T(v). -/
theorem eval_linearCoordinate (T : ComplexPlaneVector →ₗ[ℂ] ComplexPlaneVector)
    (v : ComplexPlaneVector) (j : Fin 3) :
    eval v (linearCoordinate T j) = T v j := by
  have hv : v = ∑ i : Fin 3, v i • (Pi.single i (1 : ℂ) : ComplexPlaneVector) := by
    ext k
    simp [Pi.single_apply]
  conv_rhs => rw [hv, map_sum]
  simp only [linearCoordinate, map_sum, map_mul, eval_C, eval_X,
    Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Actual polynomial evaluation commutes with the actual linear coordinate map. -/
theorem eval_linearSubstitution (T : ComplexPlaneVector →ₗ[ℂ] ComplexPlaneVector)
    (P : PlanePolynomial) (v : ComplexPlaneVector) :
    eval v (linearSubstitution T P) = eval (T v) P := by
  change aeval v (aeval (linearCoordinate T) P) = aeval (T v) P
  rw [comp_aeval_apply]
  have hg : (fun j => aeval v (linearCoordinate T j)) = T v := by
    funext j
    exact eval_linearCoordinate T v j
  rw [hg]

/-- The inverse coordinate map reverses substitution on actual polynomials. -/
theorem linearSubstitution_inverse
    (e : ComplexPlaneVector ≃ₗ[ℂ] ComplexPlaneVector) (P : PlanePolynomial) :
    linearSubstitution e.symm.toLinearMap (linearSubstitution e.toLinearMap P) = P := by
  let : Infinite ℂ := Infinite.of_injective (fun n : ℕ => (n : ℂ)) Nat.cast_injective
  apply MvPolynomial.funext
  intro v
  rw [eval_linearSubstitution, eval_linearSubstitution]
  simp

/-- Genuine invertible polynomial coordinate substitution. -/
def polynomialCoordinateEquiv (e : ComplexPlaneVector ≃ₗ[ℂ] ComplexPlaneVector) :
    PlanePolynomial ≃ₐ[ℂ] PlanePolynomial :=
  AlgEquiv.ofAlgHom (linearSubstitution e.toLinearMap) (linearSubstitution e.symm.toLinearMap)
    (by
      apply DFunLike.ext
      intro P
      exact linearSubstitution_inverse e.symm P)
    (by
      apply DFunLike.ext
      intro P
      exact linearSubstitution_inverse e P)

@[simp] theorem polynomialCoordinateEquiv_apply
    (e : ComplexPlaneVector ≃ₗ[ℂ] ComplexPlaneVector) (P : PlanePolynomial) :
    polynomialCoordinateEquiv e P = linearSubstitution e.toLinearMap P := rfl

theorem linearCoordinate_homogeneous
    (T : ComplexPlaneVector →ₗ[ℂ] ComplexPlaneVector) (j : Fin 3) :
    (linearCoordinate T j).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

/-- Linear coordinate substitution preserves the exact homogeneous degree. -/
theorem linearSubstitution_homogeneous
    (T : ComplexPlaneVector →ₗ[ℂ] ComplexPlaneVector) {P : PlanePolynomial} {d : ℕ}
    (hP : P.IsHomogeneous d) : (linearSubstitution T P).IsHomogeneous d := by
  simpa only [linearSubstitution, aeval_def, algebraMap_eq, one_mul] using
    hP.eval₂ (C : ℂ →+* PlanePolynomial) (linearCoordinate T)
      (fun r => isHomogeneous_C _ r) (linearCoordinate_homogeneous T)

/-- Invertible linear coordinates preserve and reflect homogeneous degree. -/
theorem polynomialCoordinateEquiv_homogeneous_iff
    (e : ComplexPlaneVector ≃ₗ[ℂ] ComplexPlaneVector) (P : PlanePolynomial) (d : ℕ) :
    (polynomialCoordinateEquiv e P).IsHomogeneous d ↔ P.IsHomogeneous d := by
  constructor
  · intro h
    have hh := linearSubstitution_homogeneous e.symm.toLinearMap h
    simpa only [polynomialCoordinateEquiv_apply, linearSubstitution_inverse] using hh
  · exact linearSubstitution_homogeneous e.toLinearMap

/-- Divisibility is preserved and reflected by the actual coordinate automorphism. -/
theorem polynomialCoordinateEquiv_dvd_iff
    (e : ComplexPlaneVector ≃ₗ[ℂ] ComplexPlaneVector) (P Q : PlanePolynomial) :
    polynomialCoordinateEquiv e P ∣ polynomialCoordinateEquiv e Q ↔ P ∣ Q := by
  constructor
  · intro h
    have hh := map_dvd (polynomialCoordinateEquiv e).symm h
    simpa only [AlgEquiv.symm_apply_apply] using hh
  · exact map_dvd (polynomialCoordinateEquiv e)

/-- Basis coordinates send a coordinate vector to the corresponding original vector. -/
def basisPolynomialChange (b : Basis (Fin 3) ℂ ComplexPlaneVector) :
    PlanePolynomial ≃ₐ[ℂ] PlanePolynomial := polynomialCoordinateEquiv b.equivFun.symm

@[simp] theorem basisPolynomialChange_eval
    (b : Basis (Fin 3) ℂ ComplexPlaneVector) (P : PlanePolynomial) (v : ComplexPlaneVector) :
    eval v (basisPolynomialChange b P) = eval (b.equivFun.symm v) P :=
  eval_linearSubstitution _ _ _

/-- The literal requested sum-of-coordinates substitution on each variable. -/
theorem basisPolynomialChange_X
    (b : Basis (Fin 3) ℂ ComplexPlaneVector) (j : Fin 3) :
    basisPolynomialChange b (X j) = ∑ i : Fin 3, C (b i j) * X i := by
  rw [basisPolynomialChange, polynomialCoordinateEquiv_apply, linearSubstitution_X]
  unfold linearCoordinate
  apply Finset.sum_congr rfl
  intro i _
  have hi : b.equivFun.symm (Pi.single i 1) = b i := by
    rw [b.equivFun_symm_apply]
    simp [Pi.single_apply]
  rw [show b.equivFun.symm.toLinearMap (Pi.single i 1) = b i from hi]

end Nagata.W01

end
end

section

/-! Projective and polynomial consequences of the proved actual basis normalization. -/
noncomputable section
open Module MvPolynomial
open scoped BigOperators
namespace Nagata.W01

@[simp] theorem basisPolynomialChange_homogeneous_iff
    (b : Basis (Fin 3) ℂ ComplexPlaneVector) (P : PlanePolynomial) (d : ℕ) :
    (basisPolynomialChange b P).IsHomogeneous d ↔ P.IsHomogeneous d :=
  polynomialCoordinateEquiv_homogeneous_iff b.equivFun.symm P d

@[simp] theorem basisPolynomialChange_dvd_iff
    (b : Basis (Fin 3) ℂ ComplexPlaneVector) (P Q : PlanePolynomial) :
    basisPolynomialChange b P ∣ basisPolynomialChange b Q ↔ P ∣ Q :=
  polynomialCoordinateEquiv_dvd_iff b.equivFun.symm P Q

/-- The coordinate automorphism equals the literal requested polynomial substitution. -/
theorem basisPolynomialChange_eq_eval₂
    (b : Basis (Fin 3) ℂ ComplexPlaneVector) (P : PlanePolynomial) :
    basisPolynomialChange b P =
      eval₂ C (fun j => ∑ i : Fin 3, C (b i j) * X i) P := by
  have hh : (basisPolynomialChange b).toAlgHom =
      aeval (fun j => ∑ i : Fin 3, C (b i j) * X i) := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa only [AlgEquiv.coe_toAlgHom, aeval_X] using basisPolynomialChange_X b j
  exact DFunLike.congr_fun hh P

/-- A genuine linear coordinate change induces an injective actual projective map. -/
def basisProjectiveMap (b : Basis (Fin 3) ℂ ComplexPlaneVector) :
    Projectivization ℂ ComplexPlaneVector → Projectivization ℂ ComplexPlaneVector :=
  Projectivization.map b.equivFun.toLinearMap b.equivFun.injective

theorem basisProjectiveMap_injective (b : Basis (Fin 3) ℂ ComplexPlaneVector) :
    Function.Injective (basisProjectiveMap b) :=
  Projectivization.map_injective _ _

/-- The projective coordinate map is computed from the actual chosen representative. -/
theorem basisProjectiveMap_eq_mk
    (b : Basis (Fin 3) ℂ ComplexPlaneVector) (p : Projectivization ℂ ComplexPlaneVector)
    (v : ComplexPlaneVector) (hv : v ≠ 0) (hcoord : b.equivFun p.rep = v) :
    basisProjectiveMap b p = Projectivization.mk ℂ v hv := by
  unfold basisProjectiveMap
  rw [← Projectivization.mk_rep p, Projectivization.map_mk]
  congr 1

/-- Coordinate values of the original basis vectors are exact, not merely proportional. -/
theorem basis_equivFun_vector (b : Basis (Fin 3) ℂ ComplexPlaneVector) (i : Fin 3) :
    b.equivFun (b i) = Pi.single i 1 := by
  ext j
  simp [Pi.single_apply, eq_comm]

/-- The third projective zero has two nonzero actual coordinates on the normalized line. -/
theorem exists_three_projective_zero_coordinates
    (L : ComplexPlaneVector →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (p₀ p₁ p₂ : Projectivization ℂ ComplexPlaneVector)
    (h01 : p₀ ≠ p₁) (h20 : p₂ ≠ p₀) (h21 : p₂ ≠ p₁)
    (h0 : L p₀.rep = 0) (h1 : L p₁.rep = 0) (h2 : L p₂.rep = 0) :
    ∃ (b : Basis (Fin 3) ℂ ComplexPlaneVector) (a c : ℂ),
      b 0 = p₀.rep ∧ b 1 = p₁.rep ∧ L (b 2) = 1 ∧ a ≠ 0 ∧ c ≠ 0 ∧
      b.equivFun p₀.rep = ![1, 0, 0] ∧
      b.equivFun p₁.rep = ![0, 1, 0] ∧ b.equivFun p₂.rep = ![a, c, 0] := by
  obtain ⟨b, a, c, hb0, hb1, hb2, ha, hc, hp2⟩ :=
    exists_three_projective_zeros_basis L hL p₀ p₁ p₂ h01 h20 h21 h0 h1 h2
  refine ⟨b, a, c, hb0, hb1, hb2, ha, hc, ?_, ?_, ?_⟩
  · rw [← hb0, basis_equivFun_vector]
    ext i
    fin_cases i <;> simp
  · rw [← hb1, basis_equivFun_vector]
    ext i
    fin_cases i <;> simp
  · rw [hp2, map_add, map_smul, map_smul, basis_equivFun_vector, basis_equivFun_vector]
    ext i
    fin_cases i <;> simp

/-- An arbitrary polynomial has the same value in normalized coordinates and at
the original genuine representative; in particular vanishing is transported. -/
theorem basisPolynomialChange_eval_at_coordinates
    (b : Basis (Fin 3) ℂ ComplexPlaneVector) (P : PlanePolynomial)
    (p : Projectivization ℂ ComplexPlaneVector) (v : ComplexPlaneVector)
    (hv : b.equivFun p.rep = v) :
    eval v (basisPolynomialChange b P) = eval p.rep P := by
  rw [basisPolynomialChange_eval, ← hv, LinearEquiv.symm_apply_apply]

/-- The transformed actual linear form is exactly the third variable when the
basis has linear-form values 0,0,1. -/
theorem basisPolynomialChange_linearForm_eq_X_two
    (b : Basis (Fin 3) ℂ ComplexPlaneVector)
    (L : ComplexPlaneVector →ₗ[ℂ] ℂ) (P : PlanePolynomial)
    (hP : ∀ v, eval v P = L v)
    (h0 : L (b 0) = 0) (h1 : L (b 1) = 0) (h2 : L (b 2) = 1) :
    basisPolynomialChange b P = X 2 := by
  let : Infinite ℂ := Infinite.of_injective (fun n : ℕ => (n : ℂ)) Nat.cast_injective
  apply MvPolynomial.funext
  intro v
  rw [basisPolynomialChange_eval, hP, eval_X]
  rw [← adapted_basis_third_coordinate L b h0 h1 h2]
  change b.equivFun (b.equivFun.symm v) 2 = v 2
  rw [LinearEquiv.apply_symm_apply]

end Nagata.W01

end
end

section

/-! The connected normalization theorem starts with an actual homogeneous
linear polynomial and three distinct actual projective zeros. No normalized
arrangement, linear-form representation, or coordinate-change property is assumed. -/
noncomputable section
open Module MvPolynomial
namespace Nagata.W01

/-- An actual projective linear equation and three distinct zeros admit the
proved coordinate arrangement and the literal equation X2, retaining both first reps. -/
theorem exists_homogeneous_line_normalization
    (P : PlanePolynomial) (hP : P.IsHomogeneous 1) (hne : P ≠ 0)
    (p₀ p₁ p₂ : Projectivization ℂ ComplexPlaneVector)
    (h01 : p₀ ≠ p₁) (h20 : p₂ ≠ p₀) (h21 : p₂ ≠ p₁)
    (h0 : eval p₀.rep P = 0) (h1 : eval p₁.rep P = 0) (h2 : eval p₂.rep P = 0) :
    ∃ (b : Basis (Fin 3) ℂ ComplexPlaneVector) (a c : ℂ),
      b 0 = p₀.rep ∧ b 1 = p₁.rep ∧ a ≠ 0 ∧ c ≠ 0 ∧
      b.equivFun p₀.rep = ![1, 0, 0] ∧ b.equivFun p₁.rep = ![0, 1, 0] ∧
      b.equivFun p₂.rep = ![a, c, 0] ∧ basisPolynomialChange b P = X 2 := by
  let L := Nagata.Workers.W14.homogeneousLinearMap P
  have hL : L ≠ 0 := Nagata.Workers.W14.homogeneousLinearMap_ne_zero P hP hne
  have hLeval : ∀ v, L v = eval v P :=
    Nagata.Workers.W14.homogeneousLinearMap_apply P hP
  obtain ⟨b, a, c, hb0, hb1, hb2, ha, hc, hp0, hp1, hp2⟩ :=
    exists_three_projective_zero_coordinates L hL p₀ p₁ p₂ h01 h20 h21
      ((hLeval _).trans h0) ((hLeval _).trans h1) ((hLeval _).trans h2)
  refine ⟨b, a, c, hb0, hb1, ha, hc, hp0, hp1, hp2, ?_⟩
  apply basisPolynomialChange_linearForm_eq_X_two b L P (fun v => (hLeval v).symm)
  · rw [hb0, hLeval, h0]
  · rw [hb1, hLeval, h1]
  · exact hb2

end Nagata.W01

end
end

end OAI
