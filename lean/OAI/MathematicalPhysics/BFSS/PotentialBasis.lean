import Mathlib
import OAI.MathematicalPhysics.BFSS.CliffordSymbols
import OAI.MathematicalPhysics.BFSS.MassIdentity

namespace OAI

/-! Orthogonal potential matrices and the averaged deformed bosonic potential. -/

namespace BFSSGamma
noncomputable section
open Matrix Finset
variable (G : Space → Mat)
variable (hG : ∀ i j, G i * G j + G j * G i = (if i = j then 2 else 0) • (1 : Mat))
include hG
variable (hSym : ∀ i, (G i).transpose = G i)
include hSym

abbrev SpatialPair := {p : Space × Space // p.1 < p.2}
abbrev TailIndex := {i : Space // 3 ≤ i}
def pairGamma (p : SpatialPair) : Mat := G p.1.1 * G p.1.2

def shiftedPair (h m : ℝ) (b : SpatialPair → ℝ) (x : Space → ℝ)
    (p : SpatialPair) : ℝ :=
  -h * b p + if p.1 = (0,1) then 2*m*x 2 else
    if p.1 = (0,2) then -2*m*x 1 else if p.1 = (1,2) then 2*m*x 0 else 0

def bracketMassMatrix (h m : ℝ) (b : SpatialPair → ℝ) (x : Space → ℝ) : Mat :=
  (-h) • (∑ p, b p • pairGamma G p) +
    m • (∑ i, (massWeight i * x i) • (G i * massT G))

lemma pairGamma_skew (p : SpatialPair) : (pairGamma G p).transpose = -pairGamma G p := by
  rw [pairGamma, Matrix.transpose_mul, hSym, hSym,
    gamma_anti G hG p.2.ne.symm]

lemma pairGamma_trace (p q : SpatialPair) :
    Matrix.trace ((pairGamma G p).transpose * pairGamma G q) =
      if p = q then 16 else 0 := by
  rw [pairGamma, pairGamma, ← word_pair G p.1.1 p.1.2 p.2,
    trace_dual_pair G hG hSym _ (by simp [p.2.ne]) q.1.1 q.1.2 q.2]
  congr 1
  apply propext
  constructor
  · intro heq
    obtain ⟨h1,h2⟩ := sorted_pair_unique _ _ _ _ p.2 q.2 heq
    apply Subtype.ext
    exact Prod.ext h1 h2
  · rintro rfl; rfl

lemma gamma_product_trace (i j : Space) :
    Matrix.trace (G i * G j) = if i = j then 16 else 0 := by
  have h := word_trace_dual G hG hSym {i} {j} (by simp) (by simp)
  simpa only [word_singleton G hG, hSym, Finset.singleton_inj] using h

lemma massT_mul_transpose : massT G * (massT G).transpose = 1 := by
  rw [massT_transpose G hG hSym, mul_neg, massT_sq G hG hSym, neg_neg]

lemma gammaT_trace (i j : Space) :
    Matrix.trace ((G i * massT G).transpose * (G j * massT G)) =
      if i = j then 16 else 0 := by
  rw [Matrix.transpose_mul, hSym]
  calc
    _ = Matrix.trace ((massT G * (massT G).transpose) * (G i * G j)) := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [massT_mul_transpose G hG hSym, one_mul, gamma_product_trace G hG hSym]

lemma tailGamma_symmetric (d : TailIndex) :
    (G d.1 * massT G).transpose = G d.1 * massT G := by
  have hn : ¬d.1 < 3 := not_lt.mpr d.2
  rw [Matrix.transpose_mul, massT_transpose G hG hSym, hSym, neg_mul,
    massT_gamma_comm G hG, ite_eq_right hn]
  simp

lemma pair_tail_trace (p : SpatialPair) (d : TailIndex) :
    Matrix.trace ((pairGamma G p).transpose * (G d.1 * massT G)) = 0 := by
  apply trace_skew_symm
  · rw [Matrix.transpose_transpose, pairGamma_skew G hG hSym, neg_neg]
  · exact tailGamma_symmetric G hG hSym d

omit hG hSym in
lemma dual_trace_comm (A B : Mat) :
    Matrix.trace (A.transpose * B) = Matrix.trace (B.transpose * A) := by
  rw [Matrix.trace_mul_comm]
  simpa only [Matrix.transpose_transpose] using
    (Matrix.trace_transpose_mul B.transpose A)

lemma tail_pair_trace (d : TailIndex) (p : SpatialPair) :
    Matrix.trace ((G d.1 * massT G).transpose * pairGamma G p) = 0 := by
  rw [dual_trace_comm, pair_tail_trace G hG hSym]

def potentialBasis (a : SpatialPair ⊕ TailIndex) : Mat :=
  match a with
  | .inl p => pairGamma G p
  | .inr d => G d.1 * massT G

lemma potentialBasis_trace (a b : SpatialPair ⊕ TailIndex) :
    Matrix.trace ((potentialBasis G a).transpose * potentialBasis G b) =
      if a = b then 16 else 0 := by
  cases a with
  | inl p =>
    cases b with
    | inl q => simpa only [potentialBasis, Sum.inl.injEq] using pairGamma_trace G hG hSym p q
    | inr d => simpa only [potentialBasis, Sum.inl_ne_inr, ite_false] using pair_tail_trace G hG hSym p d
  | inr d =>
    cases b with
    | inl p => simpa only [potentialBasis, Sum.inr_ne_inl, ite_false] using tail_pair_trace G hG hSym d p
    | inr e => simpa only [potentialBasis, Sum.inr.injEq, Subtype.ext_iff] using gammaT_trace G hG hSym d.1 e.1

omit hG hSym in
lemma trace_orthogonal_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Mat) (hA : ∀ i j, Matrix.trace ((A i).transpose * A j) = if i=j then 16 else 0)
    (c : ι → ℝ) :
    Matrix.trace ((∑ i, c i • A i).transpose * (∑ i, c i • A i)) =
      16 * ∑ i, c i ^ 2 := by
  simp only [Matrix.transpose_sum, Matrix.transpose_smul, Matrix.sum_mul, Matrix.mul_sum,
    smul_mul_assoc, mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, hA]
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma potential_orthogonal_sum (q : SpatialPair → ℝ) (z : TailIndex → ℝ) :
    Matrix.trace ((∑ p, q p • pairGamma G p + ∑ d, z d • (G d.1 * massT G)).transpose *
      (∑ p, q p • pairGamma G p + ∑ d, z d • (G d.1 * massT G))) =
      16 * ((∑ p, q p ^ 2) + ∑ d, z d ^ 2) := by
  have h := trace_orthogonal_sum (potentialBasis G) (potentialBasis_trace G hG hSym)
    (Sum.elim q z)
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, potentialBasis] using h

omit hSym in
lemma gamma0_massT (_hSym : ∀ index, (G index).transpose = G index) :
    G 0 * massT G = G 1 * G 2 := by
  rw [massT, ← Matrix.mul_assoc, ← Matrix.mul_assoc, gamma_sq G hG, one_mul]

omit hSym in
lemma gamma1_massT (_hSym : ∀ index, (G index).transpose = G index) :
    G 1 * massT G = -(G 0 * G 2) := by
  rw [massT, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    gamma_anti G hG (show (1 : Space) ≠ 0 by decide), neg_mul, Matrix.mul_assoc,
    gamma_sq G hG, mul_one, neg_mul]

omit hSym in
lemma gamma2_massT (_hSym : ∀ index, (G index).transpose = G index) :
    G 2 * massT G = G 0 * G 1 := by
  rw [massT, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    gamma_anti G hG (show (2 : Space) ≠ 0 by decide), neg_mul, Matrix.mul_assoc,
    gamma_anti G hG (show (2 : Space) ≠ 1 by decide), mul_neg, neg_neg,
    Matrix.mul_assoc, Matrix.mul_assoc, gamma_sq G hG, mul_one]

lemma mass_sum_decomposition (x : Space → ℝ) :
    (∑ i, (massWeight i * x i) • (G i * massT G)) =
      (2*x 2) • (G 0 * G 1) + (-2*x 1) • (G 0 * G 2) +
      (2*x 0) • (G 1 * G 2) + ∑ d : TailIndex, (-x d.1) • (G d.1 * massT G) := by
  rw [← Finset.sum_add_sum_compl firstThree]
  have ht : (∑ i ∈ firstThreeᶜ, (massWeight i * x i) • (G i * massT G)) =
      ∑ d : TailIndex, (-x d.1) • (G d.1 * massT G) := by
    rw [Finset.sum_subtype firstThreeᶜ (p := fun i : Space => 3 ≤ i)
      (by intro i; simp [mem_firstThree, not_lt])]
    apply Finset.sum_congr rfl
    intro d hd
    simp [massWeight, not_lt.mpr d.2]
  rw [ht]
  congr 1
  rw [firstThree, Finset.sum_insert (by decide : (0 : Space) ∉ ({(1 : Space),(2 : Space)} : Finset Space)),
    Finset.sum_insert (by decide : (1 : Space) ∉ ({(2 : Space)} : Finset Space)),
    Finset.sum_singleton]
  rw [gamma0_massT G hG hSym, gamma1_massT G hG hSym, gamma2_massT G hG hSym]
  norm_num only [massWeight, show (0 : Space) < 3 by decide,
    show (1 : Space) < 3 by decide, show (2 : Space) < 3 by decide, ite_true]
  simp only [smul_neg, neg_mul, neg_smul]
  abel

omit G hG hSym in
def pair01 : SpatialPair := ⟨(0,1), by decide⟩
omit G hG hSym in
def pair02 : SpatialPair := ⟨(0,2), by decide⟩
omit G hG hSym in
def pair12 : SpatialPair := ⟨(1,2), by decide⟩

omit hG hSym in
lemma shiftedPair_sum (h m : ℝ) (b : SpatialPair → ℝ) (x : Space → ℝ) :
    (∑ p, shiftedPair h m b x p • pairGamma G p) =
      (-h) • (∑ p, b p • pairGamma G p) +
      (2*m*x 2) • (G 0 * G 1) + (-2*m*x 1) • (G 0 * G 2) +
      (2*m*x 0) • (G 1 * G 2) := by
  have he (p : SpatialPair) : shiftedPair h m b x p = -h*b p +
      (if p = pair01 then 2*m*x 2 else 0) +
      (if p = pair02 then -2*m*x 1 else 0) +
      (if p = pair12 then 2*m*x 0 else 0) := by
    have e01 : p = pair01 ↔ p.1 = (0,1) := Subtype.ext_iff
    have e02 : p = pair02 ↔ p.1 = (0,2) := Subtype.ext_iff
    have e12 : p = pair12 ↔ p.1 = (1,2) := Subtype.ext_iff
    simp only [e01, e02, e12, shiftedPair]
    split_ifs <;> simp_all
  simp only [he, add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum,
    ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

lemma bracketMass_decomposition (h m : ℝ) (b : SpatialPair → ℝ) (x : Space → ℝ) :
    bracketMassMatrix G h m b x =
      (∑ p, shiftedPair h m b x p • pairGamma G p) +
      ∑ d : TailIndex, (-m*x d.1) • (G d.1 * massT G) := by
  rw [bracketMassMatrix, mass_sum_decomposition G hG hSym, shiftedPair_sum]
  simp only [smul_add, smul_smul, Finset.smul_sum]
  simp only [mul_neg, neg_mul]
  module

lemma bracketMass_trace_square (h m : ℝ) (b : SpatialPair → ℝ) (x : Space → ℝ) :
    Matrix.trace ((bracketMassMatrix G h m b x).transpose * bracketMassMatrix G h m b x) =
      16 * ((∑ p, (shiftedPair h m b x p)^2) + ∑ d : TailIndex, (m*x d.1)^2) := by
  rw [bracketMass_decomposition G hG hSym, potential_orthogonal_sum G hG hSym]
  simp only [neg_mul, neg_sq]

end
end BFSSGamma

namespace BFSSQuantum
noncomputable section
open Matrix Finset
namespace AlgebraData
variable {N : ℕ} (M : AlgebraData N)

abbrev SpatialPair := BFSSGamma.SpatialPair
abbrev TailIndex := BFSSGamma.TailIndex

def coordinateBracket (x : Boson N) (p : SpatialPair) (A : ColorIndex N) : ℝ :=
  ∑ B, ∑ C, M.structureConstant A B C * x (p.1.1,B) * x (p.1.2,C)

def deformedPotentialMatrix (h m : ℝ) (x : Boson N) (A : ColorIndex N) : GammaMatrix :=
  BFSSGamma.bracketMassMatrix M.gamma h m (fun p => M.coordinateBracket x p A)
    (fun i => x (i,A))

def deformedPotentialCoefficients (h m : ℝ) (x : Boson N) (α : SpinIndex) :
    FermionIndex N → ℝ :=
  fun p => M.deformedPotentialMatrix h m x p.2 p.1 α

def deformedPotentialMultiplier (h m : ℝ) (x : Boson N) (α : SpinIndex) :
    Fermion N →L[ℂ] Fermion N :=
  M.cliffordLinear (M.deformedPotentialCoefficients h m x α)

def deformedBosonicPotential (h m : ℝ) (x : Boson N) : ℝ :=
  (1/2 : ℝ) * ∑ A : ColorIndex N,
    ((∑ p : SpatialPair,
      (BFSSGamma.shiftedPair h m (fun p => M.coordinateBracket x p A) (fun i => x (i,A)) p)^2) +
      ∑ d : TailIndex, (m*x (d.1,A))^2)

lemma deformedPotentialMatrix_trace (h m : ℝ) (x : Boson N) (A : ColorIndex N) :
    Matrix.trace ((M.deformedPotentialMatrix h m x A).transpose * M.deformedPotentialMatrix h m x A) =
      16 * ((∑ p : SpatialPair,
        (BFSSGamma.shiftedPair h m (fun p => M.coordinateBracket x p A) (fun i => x (i,A)) p)^2) +
        ∑ d : TailIndex, (m*x (d.1,A))^2) :=
  BFSSGamma.bracketMass_trace_square M.gamma M.gamma_clifford M.gamma_symmetric h m
    (fun p => M.coordinateBracket x p A) (fun i => x (i,A))

lemma deformedPotentialCoefficients_total (h m : ℝ) (x : Boson N) :
    (∑ α, ∑ p : FermionIndex N, (M.deformedPotentialCoefficients h m x α p)^2) =
      32 * M.deformedBosonicPotential h m x := by
  simp only [deformedPotentialCoefficients, Fintype.sum_prod_type]
  calc
    _ = ∑ α, ∑ A : ColorIndex N, ∑ β : SpinIndex,
        (M.deformedPotentialMatrix h m x A β α)^2 := by
      apply Finset.sum_congr rfl
      intro α hα
      exact Finset.sum_comm
    _ = ∑ A : ColorIndex N, ∑ α : SpinIndex, ∑ β : SpinIndex,
        (M.deformedPotentialMatrix h m x A β α)^2 := Finset.sum_comm
    _ = ∑ A : ColorIndex N,
        Matrix.trace ((M.deformedPotentialMatrix h m x A).transpose * M.deformedPotentialMatrix h m x A) := by
      apply Finset.sum_congr rfl
      intro A hA
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
    _ = _ := by
      simp only [M.deformedPotentialMatrix_trace, deformedBosonicPotential, ← Finset.mul_sum]
      ring

theorem deformed_potential_average (h m : ℝ) (x : Boson N) (z : Fermion N) :
    (1/16 : ℝ) * ∑ α : SpinIndex, ‖M.deformedPotentialMultiplier h m x α z‖^2 =
      M.deformedBosonicPotential h m x * ‖z‖^2 := by
  simp only [deformedPotentialMultiplier, M.cliffordLinear_norm_sq,
    ← Finset.sum_mul, ← Finset.mul_sum]
  rw [M.deformedPotentialCoefficients_total]
  ring

end AlgebraData
end
end BFSSQuantum

end OAI
