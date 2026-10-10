import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.Matrix

namespace OAI

/-!
# Basis coordinates, maximal minors, and limits of finite matrices
-/

section

/-! Genuine basis-coordinate identities for finite jet matrices. -/
noncomputable section
open Module
namespace Nagata.Workers.W11
variable {ι κ V K : Type*} [Field K] [Fintype ι] [AddCommGroup V] [Module K V]

/-- The matrix of a linear jet map is its values on a genuine domain basis. -/
def basisJetMatrix (e : Basis ι K V) (J : V →ₗ[K] (κ → K)) : Matrix κ ι K :=
  fun row col => J (e col) row

/-- Evaluating the basis matrix on a coordinate vector recovers the original
linear map, by the finite basis expansion of the vector. -/
theorem basisJetMatrix_mulVec_repr (e : Basis ι K V) (J : V →ₗ[K] (κ → K)) (v : V) :
    (basisJetMatrix e J).mulVec (e.repr v) = J v := by
  funext row
  have h := congrFun (congrArg J (e.sum_repr v)) row
  simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    basisJetMatrix, Matrix.mulVec, dotProduct, mul_comm] using h

/-- Injectivity of the numerical matrix implies injectivity of the original
linear jet map in its genuine vector space. -/
theorem injective_of_basisJetMatrix (e : Basis ι K V) (J : V →ₗ[K] (κ → K))
    (h : Function.Injective (basisJetMatrix e J).mulVec) : Function.Injective J := by
  intro v w hvw
  apply e.repr.injective
  apply Finsupp.ext
  intro i
  have hc : (fun i => e.repr v i) = (fun i => e.repr w i) := h (by
    rw [basisJetMatrix_mulVec_repr, basisJetMatrix_mulVec_repr, hvw])
  exact congrFun hc i

/-- A nonzero kernel vector of the original jet map becomes a nonzero kernel
coordinate vector. This proves the noncancellation bridge for a genuine basis. -/
theorem basisJetMatrix_nonzero_kernel (e : Basis ι K V) (J : V →ₗ[K] (κ → K))
    (v : V) (hv : v ≠ 0) (hJ : J v = 0) :
    ∃ c : ι → K, c ≠ 0 ∧ (basisJetMatrix e J).mulVec c = 0 := by
  refine ⟨e.repr v, ?_, by rw [basisJetMatrix_mulVec_repr, hJ]⟩
  intro hc
  apply hv
  apply e.repr.injective
  apply Finsupp.ext
  intro i
  simpa using congrFun hc i

end Nagata.Workers.W11

end
end

section

/-!
# Persistence of injectivity in the limiting jet matrix
-/

open Filter Topology

namespace Nagata.Workers.W11

variable {α ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise convergence of finite square complex matrices implies convergence
of their determinants. The parameter filter can in particular be `𝓝[>] 0`. -/
theorem tendsto_det_of_entrywise {l : Filter α}
    {B : α → Matrix ι ι ℂ} {B₀ : Matrix ι ι ℂ}
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j))) :
    Tendsto (fun t => (B t).det) l (𝓝 B₀.det) := by
  have h : Tendsto B l (𝓝 B₀) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (hB i))
  exact (continuous_id.matrix_det.continuousAt.tendsto).comp h

/-- A nonzero limiting determinant remains nonzero eventually. -/
theorem eventually_det_ne_zero_of_entrywise {l : Filter α}
    {B : α → Matrix ι ι ℂ} {B₀ : Matrix ι ι ℂ}
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j)))
    (h₀ : B₀.det ≠ 0) : ∀ᶠ t in l, (B t).det ≠ 0 :=
  (tendsto_det_of_entrywise hB).eventually_ne h₀

/-- A square matrix family with nonzero limiting determinant is eventually
injective as a map on coefficient vectors. -/
theorem eventually_injective_of_entrywise {l : Filter α}
    {B : α → Matrix ι ι ℂ} {B₀ : Matrix ι ι ℂ}
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j)))
    (h₀ : B₀.det ≠ 0) : ∀ᶠ t in l, Function.Injective (B t).mulVec := by
  exact (eventually_det_ne_zero_of_entrywise hB h₀).mono fun t ht =>
    Matrix.mulVec_injective_of_isUnit
      ((B t).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr ht))

/-- The rectangular version used by the manuscript: an explicit square row
minor with nonzero limiting determinant suffices. No finiteness assumption on
the row set is needed for this implication. -/
theorem eventually_injective_of_nonzero_minor {l : Filter α}
    {B : α → Matrix κ ι ℂ} {B₀ : Matrix κ ι ℂ} (row : ι → κ)
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j)))
    (h₀ : (B₀.submatrix row id).det ≠ 0) :
    ∀ᶠ t in l, Function.Injective (B t).mulVec := by
  have hminor : ∀ᶠ t in l,
      Function.Injective ((B t).submatrix row id).mulVec :=
    eventually_injective_of_entrywise (fun i j => hB (row i) j) h₀
  exact hminor.mono fun t ht x y hxy => ht (by
    funext i
    exact congrFun hxy (row i))

/-- Multiplication by a fixed left inverse reduces the rectangular problem to
the square determinant theorem. -/
theorem eventually_injective_of_left_inverse [Fintype κ]
    {l : Filter α} {B : α → Matrix κ ι ℂ} {B₀ : Matrix κ ι ℂ}
    (C : Matrix ι κ ℂ) (hC : C * B₀ = 1)
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j))) :
    ∀ᶠ t in l, Function.Injective (B t).mulVec := by
  have h : Tendsto B l (𝓝 B₀) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (hB i))
  have hmul : Tendsto (fun t => C * B t) l (𝓝 (C * B₀)) :=
    ((continuous_const.matrix_mul continuous_id).continuousAt.tendsto).comp h
  have hentry : ∀ i j, Tendsto (fun t => (C * B t) i j) l (𝓝 ((C * B₀) i j)) :=
    fun i j => tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hmul i) j
  have hdet : (C * B₀).det ≠ 0 := by simp [hC]
  exact (eventually_injective_of_entrywise hentry hdet).mono fun t ht x y hxy =>
    ht (by simpa only [Matrix.mulVec_mulVec] using congrArg C.mulVec hxy)

/-- Full column rank of the limiting finite complex matrix implies eventual
full column rank under entrywise convergence. This closes the finite-matrix
implication in `prop:matrix-limit` without assuming a preselected minor. -/
theorem eventually_injective_of_injective_limit [Fintype κ] [DecidableEq κ]
    {l : Filter α} {B : α → Matrix κ ι ℂ} {B₀ : Matrix κ ι ℂ}
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j)))
    (h₀ : Function.Injective B₀.mulVec) :
    ∀ᶠ t in l, Function.Injective (B t).mulVec := by
  obtain ⟨g, hg⟩ := (Matrix.toLin' B₀).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr h₀)
  have hC : LinearMap.toMatrix' g * B₀ = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  exact eventually_injective_of_left_inverse (LinearMap.toMatrix' g) hC hB

/-- Collision supplies nonzero kernel vectors independently for each parameter;
their continuity is unnecessary. Together with an injective limiting matrix,
even eventual existence of such vectors is impossible. -/
theorem not_eventually_nonzero_kernel_of_injective_limit
    [Fintype κ] [DecidableEq κ] {l : Filter α} [NeBot l]
    {B : α → Matrix κ ι ℂ} {B₀ : Matrix κ ι ℂ}
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j)))
    (h₀ : Function.Injective B₀.mulVec) :
    ¬ (∀ᶠ t in l, ∃ v : ι → ℂ, v ≠ 0 ∧ (B t).mulVec v = 0) := by
  intro hker
  obtain ⟨t, ht, v, hv, hzero⟩ :=
    ((eventually_injective_of_injective_limit hB h₀).and hker).exists
  exact hv (ht (by simpa only [Matrix.mulVec_zero] using hzero))

end Nagata.Workers.W11

end

section

/-!
# Vanishing maximal minors and nonzero kernel vectors
-/

namespace Nagata.Workers.W11

variable {ρ κ K : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]

/-- If every maximal row minor of a rectangular matrix vanishes, multiplying
on the left by any matrix to make it square still gives determinant zero. -/
theorem det_mul_eq_zero_of_all_maximal_minors_zero [CommRing K]
    (A : Matrix ρ κ K) (C : Matrix κ ρ K)
    (hA : ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0) :
    (C * A).det = 0 := by
  classical
  let D : MultilinearMap K (fun _ : κ => κ → K) K :=
    Matrix.detRowAlternating.toMultilinearMap
  have hmul : C * A = fun i => ∑ r, C i r • A r := by
    funext i j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change D (C * A) = 0
  rw [hmul, D.map_sum]
  apply Finset.sum_eq_zero
  intro s _
  rw [D.map_smul_univ]
  change (∏ i, C i (s i)) • Matrix.det (fun i j => A (s i) j) = 0
  rw [hA s, smul_zero]

/-- A finite rectangular matrix over a field whose maximal row minors all
vanish has a nonzero vector in its kernel. No nonempty-column assumption is
necessary: in zero columns the hypothesis itself is false. -/
theorem exists_nonzero_kernel_of_all_maximal_minors_zero [Field K]
    (A : Matrix ρ κ K)
    (hA : ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0) :
    ∃ c : κ → K, c ≠ 0 ∧ A.mulVec c = 0 := by
  classical
  by_contra hkernel
  have hker : LinearMap.ker (Matrix.toLin' A) = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    by_contra hc0
    exact hkernel ⟨c, hc0, hc⟩
  obtain ⟨g, hg⟩ := (Matrix.toLin' A).exists_leftInverse_of_injective hker
  have hC : LinearMap.toMatrix' g * A = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  have hdet := det_mul_eq_zero_of_all_maximal_minors_zero A (LinearMap.toMatrix' g) hA
  rw [hC, Matrix.det_one] at hdet
  exact one_ne_zero hdet

/-- Coordinate form matching the affine-jet incidence interface. -/
theorem exists_nonzero_kernel_coordinates_of_all_maximal_minors_zero [Field K]
    (A : Matrix ρ κ K)
    (hA : ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0) :
    ∃ c : κ → K, c ≠ 0 ∧ ∀ i, ∑ j, A i j * c j = 0 := by
  obtain ⟨c, hc, hAc⟩ := exists_nonzero_kernel_of_all_maximal_minors_zero A hA
  exact ⟨c, hc, fun i => congrFun hAc i⟩

/-- In an underdetermined finite matrix every maximal row selection repeats a
row, so all its maximal minors vanish. This includes the empty-row case. -/
theorem all_maximal_minors_zero_of_card_lt [CommRing K]
    (A : Matrix ρ κ K) (hcard : Fintype.card ρ < Fintype.card κ) :
    ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0 := by
  intro s
  have hs : ¬ Function.Injective s := fun hs =>
    (not_le_of_gt hcard) (Fintype.card_le_of_injective s hs)
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hs
  exact Matrix.det_zero_of_row_eq (M := fun i j => A (s i) j) hne (congrArg A hij)

/-- Fewer equations than unknowns gives a nonzero solution, using exactly the
same maximal-minor criterion as the incidence construction. -/
theorem exists_nonzero_kernel_of_fewer_rows [Field K]
    (A : Matrix ρ κ K) (hcard : Fintype.card ρ < Fintype.card κ) :
    ∃ c : κ → K, c ≠ 0 ∧ A.mulVec c = 0 :=
  exists_nonzero_kernel_of_all_maximal_minors_zero A
    (all_maximal_minors_zero_of_card_lt A hcard)

omit [Fintype ρ] [DecidableEq κ] in
/-- With no unknowns there is no nonzero coefficient vector, as required by
the nonzero-curve incidence convention. -/
theorem not_nonzero_kernel_of_isEmpty_columns [CommRing K] [IsEmpty κ]
    (A : Matrix ρ κ K) : ¬ ∃ c : κ → K, c ≠ 0 ∧ A.mulVec c = 0 := by
  rintro ⟨c, hc, _⟩
  exact hc (Subsingleton.elim _ _)

omit [Fintype ρ] in
/-- With no unknowns the unique zero-by-zero maximal minor is one, so the
determinantal vanishing condition is false over a nontrivial ring. -/
theorem not_all_maximal_minors_zero_of_isEmpty_columns
    [CommRing K] [Nontrivial K] [IsEmpty κ]
    (A : Matrix ρ κ K) :
    ¬ ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0 := by
  intro h
  have hz := h (fun i => isEmptyElim i)
  exact (one_ne_zero : (1 : K) ≠ 0) (Matrix.det_isEmpty.symm.trans hz)

/-- The exact nonzero-minor existence statement used in the manuscript's
matrix-limit proof, derived from injectivity rather than assumed. -/
theorem exists_nonzero_maximal_minor_of_injective [Field K]
    (A : Matrix ρ κ K) (hA : Function.Injective A.mulVec) :
    ∃ s : κ → ρ, Matrix.det (fun i j => A (s i) j) ≠ 0 := by
  classical
  by_contra hminor
  have hzero : ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0 :=
    fun s => not_not.mp (not_exists.mp hminor s)
  obtain ⟨c, hc, hAc⟩ := exists_nonzero_kernel_of_all_maximal_minors_zero A hzero
  exact hc (hA (by simpa only [Matrix.mulVec_zero] using hAc))

end Nagata.Workers.W11

end

end OAI
