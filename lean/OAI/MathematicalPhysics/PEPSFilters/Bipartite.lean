import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.Phases

namespace OAI

/-! Bipartite physical states and finite Schmidt decompositions. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set

open scoped BigOperators Matrix.Norms.L2Operator
namespace PolynomialPEPS.PinnedEntropy
open Matrix
variable {L q : ℕ}

def tensorState (A : Finset (Vertex L))
    (e : EuclideanSpace ℂ (RegionConfiguration q A))
    (f : EuclideanSpace ℂ (RegionConfiguration q Aᶜ)) : State L q :=
  WithLp.toLp 2 (fun x => e (restrictConfiguration A x) * f (restrictConfiguration Aᶜ x))

lemma coefficientMatrix_tensorState (A : Finset (Vertex L))
    (e : EuclideanSpace ℂ (RegionConfiguration q A))
    (f : EuclideanSpace ℂ (RegionConfiguration q Aᶜ)) (x z) :
    coefficientMatrix (tensorState A e f) A x z = e x * f z := by
  simp [coefficientMatrix, tensorState]

lemma inner_tensorState (A : Finset (Vertex L))
    (e g : EuclideanSpace ℂ (RegionConfiguration q A))
    (f h : EuclideanSpace ℂ (RegionConfiguration q Aᶜ)) :
    inner ℂ (tensorState A e f) (tensorState A g h) = inner ℂ e g * inner ℂ f h := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  rw [← (splitConfigurations (q := q) A).symm.sum_comp, Fintype.sum_prod_type]
  simp only [splitConfigurations, Equiv.coe_fn_symm_mk, tensorState, Pi.star_apply,
    restrict_join_left, restrict_join_right, WithLp.ofLp_toLp]
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro z _
  simp only [Pi.star_apply, star_mul]
  ring

lemma asMap_liftLocal_tensorState (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (e : EuclideanSpace ℂ (RegionConfiguration q A))
    (f : EuclideanSpace ℂ (RegionConfiguration q Aᶜ)) :
    asMap (liftLocal A B) (tensorState A e f) = tensorState A ((Matrix.toEuclideanCLM (𝕜 := ℂ) B) e) f := by
  apply coefficientMatrix_injective A
  dsimp only
  rw [coefficientMatrix_asMap_liftLocal]
  ext x z
  simp only [Matrix.mul_apply, coefficientMatrix_tensorState]
  change ∑ y, B x y * (e y * f z) = (∑ y, B x y * e y) * f z
  simp only [Finset.sum_mul, mul_assoc]

lemma liftComplement_apply_join (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q Aᶜ) (RegionConfiguration q Aᶜ) ℂ)
    (x y : RegionConfiguration q A) (z w : RegionConfiguration q Aᶜ) :
    liftLocal Aᶜ B (joinConfigurations A x z) (joinConfigurations A y w) =
      if x = y then B z w else 0 := by
  classical
  have hag : (∀ v, v ∉ Aᶜ → joinConfigurations A x z v = joinConfigurations A y w v) ↔ x = y := by
    constructor
    · intro h
      funext v
      simpa [joinConfigurations, v.property] using h v.val (by simp)
    · rintro rfl v hv
      have hvA : v ∈ A := by simpa using hv
      simp [joinConfigurations, hvA]
  change (if ∀ v, v ∉ Aᶜ → joinConfigurations A x z v = joinConfigurations A y w v then
    B (restrictConfiguration Aᶜ (joinConfigurations A x z))
      (restrictConfiguration Aᶜ (joinConfigurations A y w)) else 0) = _
  simp only [hag, restrict_join_right]

lemma coefficientMatrix_asMap_liftComplement (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q Aᶜ) (RegionConfiguration q Aᶜ) ℂ)
    (v : State L q) :
    coefficientMatrix (asMap (liftLocal Aᶜ B) v) A = coefficientMatrix v A * B.transpose := by
  classical
  ext x z
  rw [coefficientMatrix, asMap_apply]
  rw [← (splitConfigurations (q := q) A).symm.sum_comp]
  simp only [Fintype.sum_prod_type, splitConfigurations, Equiv.coe_fn_symm_mk,
    liftComplement_apply_join, ite_mul, zero_mul]
  simp [Matrix.mul_apply, coefficientMatrix, mul_comm]

lemma asMap_liftComplement_tensorState (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q Aᶜ) (RegionConfiguration q Aᶜ) ℂ)
    (e : EuclideanSpace ℂ (RegionConfiguration q A))
    (f : EuclideanSpace ℂ (RegionConfiguration q Aᶜ)) :
    asMap (liftLocal Aᶜ B) (tensorState A e f) = tensorState A e ((Matrix.toEuclideanCLM (𝕜 := ℂ) B) f) := by
  apply coefficientMatrix_injective A
  dsimp only
  rw [coefficientMatrix_asMap_liftComplement]
  ext x z
  simp only [Matrix.mul_apply, coefficientMatrix_tensorState, Matrix.transpose_apply]
  change ∑ w, (e x * f w) * B z w = e x * (∑ w, B z w * f w)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w _
  ring

lemma inner_tensorState_productOperator (A : Finset (Vertex L))
    (B : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (C : Matrix (RegionConfiguration q Aᶜ) (RegionConfiguration q Aᶜ) ℂ)
    (e g : EuclideanSpace ℂ (RegionConfiguration q A))
    (f h : EuclideanSpace ℂ (RegionConfiguration q Aᶜ)) :
    inner ℂ (tensorState A e f) (asMap (liftLocal A B * liftLocal Aᶜ C) (tensorState A g h)) =
      inner ℂ e ((Matrix.toEuclideanCLM (𝕜 := ℂ) B) g) * inner ℂ f ((Matrix.toEuclideanCLM (𝕜 := ℂ) C) h) := by
  rw [asMap_mul, asMap_liftComplement_tensorState, asMap_liftLocal_tensorState, inner_tensorState]
end PolynomialPEPS.PinnedEntropy

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Matrix
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def columnVector (U : Matrix n n ℂ) (i : n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun x => U x i)
def rowVector (D : Matrix n m ℂ) (i : n) : EuclideanSpace ℂ m :=
  WithLp.toLp 2 (fun x => D i x)

omit [DecidableEq n] in
lemma inner_columnVector (U : Matrix n n ℂ) (i k : n) :
    inner ℂ (columnVector U i) (columnVector U k) = (star U * U) i k := by
  simp only [columnVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Pi.star_apply, mul_comm]

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
lemma inner_rowVector (D : Matrix n m ℂ) (i k : n) :
    inner ℂ (rowVector D i) (rowVector D k) = (D * D.conjTranspose) k i := by
  simp only [rowVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply]

lemma orthonormal_columns (U : unitary (Matrix n n ℂ)) :
    Orthonormal ℂ (columnVector (U : Matrix n n ℂ)) := by
  rw [orthonormal_iff_ite]
  intro i k
  rw [inner_columnVector, U.property.1]
  rfl

abbrev schmidtIndex (r : n → ℝ) := {i : n // 0 < r i}
local instance bipartiteSchmidtIndexDecidable (r : n → ℝ) :
    DecidablePred (fun i => 0 < r i) := Classical.decPred _

def schmidtRight (D : Matrix n m ℂ) (r : n → ℝ) (i : schmidtIndex r) : EuclideanSpace ℂ m :=
  ((Real.sqrt (r i) : ℂ)⁻¹) • rowVector D i

omit [Fintype n] [DecidableEq m] in
lemma orthonormal_schmidtRight (D : Matrix n m ℂ) (r : n → ℝ)
    (hD : D * D.conjTranspose = Matrix.diagonal (fun i => (r i : ℂ))) :
    Orthonormal ℂ (schmidtRight D r) := by
  classical
  rw [orthonormal_iff_ite]
  intro i k
  simp only [schmidtRight, inner_smul_left, inner_smul_right, inner_rowVector, hD,
    map_inv₀, Complex.conj_ofReal]
  by_cases hik : i = k
  · subst k
    simp only [Matrix.diagonal_apply_eq, ite_true]
    have hs : (Real.sqrt (r i) : ℂ) ^ 2 = (r i : ℂ) := by
      exact_mod_cast Real.sq_sqrt i.property.le
    have hn : (Real.sqrt (r i) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr i.property).ne'
    field_simp
    exact hs.symm
  · have hv : (k : n) ≠ (i : n) := fun h => hik (Subtype.ext h.symm)
    simp only [Matrix.diagonal_apply_ne _ hv, mul_zero, ite_eq_right hik]

omit [Fintype n] [DecidableEq m] in
lemma rowVector_zero_of_diagonal_zero (D : Matrix n m ℂ) (r : n → ℝ)
    (hD : D * D.conjTranspose = Matrix.diagonal (fun i => (r i : ℂ))) (i : n) (hi : r i = 0) :
    rowVector D i = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_rowVector, hD, Matrix.diagonal_apply_eq, hi, Complex.ofReal_zero]

omit [DecidableEq m] in
lemma schmidt_reconstruct_entry (U : unitary (Matrix n n ℂ)) (D : Matrix n m ℂ)
    (r : n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hD : D * D.conjTranspose = Matrix.diagonal (fun i => (r i : ℂ))) (x : n) (y : m) :
    ((U : Matrix n n ℂ) * D) x y =
      ∑ i : schmidtIndex r, (Real.sqrt (r i) : ℂ) * columnVector (U : Matrix n n ℂ) i x * schmidtRight D r i y := by
  classical
  have ht (i : schmidtIndex r) :
      (Real.sqrt (r i) : ℂ) * columnVector (U : Matrix n n ℂ) i x * schmidtRight D r i y =
        (U : Matrix n n ℂ) x i * D i y := by
    simp only [columnVector, schmidtRight, rowVector, PiLp.smul_apply,
      smul_eq_mul]
    have hn : (Real.sqrt (r i) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr i.property).ne'
    field_simp
  simp_rw [ht]
  rw [Matrix.mul_apply]
  symm
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => 0 < r i) (fun i => (U : Matrix n n ℂ) x i * D i y)]
  suffices (∑ i : {i : n // ¬0 < r i}, (U : Matrix n n ℂ) x i * D i y) = 0 by rw [this, add_zero]
  apply Finset.sum_eq_zero
  intro ii _
  let i : n := ii.val
  have hi : ¬0 < r i := ii.property
  have hir : r i = 0 := le_antisymm (le_of_not_gt hi) (hr i)
  have hh := congrArg (fun v : EuclideanSpace ℂ m => v y) (rowVector_zero_of_diagonal_zero D r hD i hir)
  change D i y = 0 at hh
  change (U : Matrix n n ℂ) x i * D i y = 0
  simp only [hh, mul_zero]

omit [DecidableEq m] in
lemma rotated_density_diagonal (C : Matrix n m ℂ) (U : unitary (Matrix n n ℂ))
    (r : n → ℝ)
    (hC : C * C.conjTranspose = Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => (r i : ℂ)))) :
    (star (U : Matrix n n ℂ) * C) * (star (U : Matrix n n ℂ) * C).conjTranspose =
      Matrix.diagonal (fun i => (r i : ℂ)) := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  change star (U : Matrix n n ℂ) * C * (C.conjTranspose * (U : Matrix n n ℂ)) = _
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, hC,
    Unitary.conjStarAlgAut_apply]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star (U : Matrix n n ℂ)) (U : Matrix n n ℂ),
    U.property.1, Matrix.one_mul, Matrix.mul_one]

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Matrix
variable {L q : ℕ}

lemma physical_schmidt_decomposition (A : Finset (Vertex L)) (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ))
    (r : RegionConfiguration q A → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hρ : reducedDensity ψ A = Unitary.conjStarAlgAut ℂ _ U
      (Matrix.diagonal (fun i => (r i : ℂ)))) :
    ψ = ∑ i : schmidtIndex r, (Real.sqrt (r i) : ℂ) •
      tensorState A (columnVector (U : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) i)
        (schmidtRight (star (U : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) * coefficientMatrix ψ A) r i) := by
  classical
  let D := star (U : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) * coefficientMatrix ψ A
  have hD := rotated_density_diagonal (coefficientMatrix ψ A) U r hρ
  have hUD : (U : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) * D = coefficientMatrix ψ A := by
    dsimp only [D]
    rw [← Matrix.mul_assoc, U.property.2, Matrix.one_mul]
  apply coefficientMatrix_injective A
  dsimp only
  ext x y
  trans ((U : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) * D) x y
  · exact congrFun (congrFun hUD.symm x) y
  rw [schmidt_reconstruct_entry U D r hr hD]
  change (∑ i : schmidtIndex r, _) =
    (∑ i : schmidtIndex r, (Real.sqrt (r i) : ℂ) •
      tensorState A (columnVector (U : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) i) (schmidtRight D r i)) (joinConfigurations A x y)
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change (Real.sqrt (r i) : ℂ) * columnVector (U : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) i x * schmidtRight D r i y =
    (Real.sqrt (r i) : ℂ) * coefficientMatrix (tensorState A (columnVector (U : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) i) (schmidtRight D r i)) A x y
  rw [coefficientMatrix_tensorState, mul_assoc]

lemma sum_schmidt_probabilities (A : Finset (Vertex L)) (ψ : State L q)
    (hψ : ‖ψ‖ = 1)
    (U : unitary (Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ))
    (r : RegionConfiguration q A → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hρ : reducedDensity ψ A = Unitary.conjStarAlgAut ℂ _ U
      (Matrix.diagonal (fun i => (r i : ℂ)))) :
    ∑ i : schmidtIndex r, r i = 1 := by
  classical
  have ht := congrArg (fun B => (Matrix.trace B).re) hρ
  rw [trace_reducedDensity, hψ] at ht
  simp only [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    U.property.1, Matrix.one_mul, Matrix.trace_diagonal, ← Complex.ofReal_sum,
    Complex.ofReal_re] at ht
  norm_num at ht
  rw [ht]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => 0 < r i) r]
  have hz : (∑ i : {i : RegionConfiguration q A // ¬0 < r i}, r i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact le_antisymm (le_of_not_gt i.property) (hr i)
  rw [hz, add_zero]

lemma diagonal_conjugate_column {n : Type*} [Fintype n] [DecidableEq n] (U : unitary (Matrix n n ℂ))
    (l : n → ℝ) (i : n) :
    Matrix.toEuclideanCLM (𝕜 := ℂ)
      (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun k => (l k : ℂ))))
        (columnVector (U : Matrix n n ℂ) i) = (l i : ℂ) • columnVector (U : Matrix n n ℂ) i := by
  classical
  have hm := congrArg (fun B : Matrix n n ℂ => fun x => B x i)
    (show (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun k => (l k : ℂ)))) * (U : Matrix n n ℂ) =
      (U : Matrix n n ℂ) * Matrix.diagonal (fun k => (l k : ℂ)) by
      rw [Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, U.property.1, Matrix.mul_one])
  ext x
  have he := congrFun hm x
  rw [Matrix.mul_diagonal] at he
  change (∑ j, (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun k => (l k : ℂ)))) x j * (U : Matrix n n ℂ) j i) =
    (l i : ℂ) * (U : Matrix n n ℂ) x i
  exact he.trans (mul_comm _ _)

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

end

end OAI
