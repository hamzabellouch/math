import OAI.NumberTheory.DukePrimeDegree.Dynamics.PrimeBlockEndpoint
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

namespace OAI

/-!
# Rationality of matrix centralizers

The commutant of a finite collection of rational matrices is spanned over
the reals by its rational matrices. This is the linear algebra part of
the homogeneous-orbit rationality step: it uses exactness of scalar
extension, and does not assert that a lattice stabilizer is dense in a
block group.
-/

noncomputable section
open Matrix Module Set
open scoped Classical

namespace DukePrimeDegree

section Kernel

variable {V U V' U' : Type*}
  [AddCommGroup V] [Module ℚ V] [AddCommGroup U] [Module ℚ U]
  [AddCommGroup V'] [Module ℚ V'] [Module ℝ V'] [IsScalarTower ℚ ℝ V']
  [AddCommGroup U'] [Module ℚ U'] [Module ℝ U'] [IsScalarTower ℚ ℝ U']

/-- Exact scalar extension expresses every real kernel vector as a real
linear combination of rational kernel vectors. -/
private theorem kernel_spanned_of_baseChange
    (f : V →ₗ[ℚ] U) (f' : V' →ₗ[ℝ] U')
    (cV : V →ₗ[ℚ] V') (cU : U →ₗ[ℚ] U')
    (hV : IsBaseChange ℝ cV) (hU : IsBaseChange ℝ cU)
    (hcomm : cU.comp f = (f'.restrictScalars ℚ).comp cV) :
    f'.ker = Submodule.span ℝ (cV '' (f.ker : Set V)) := by
  let k : f.ker →ₗ[ℚ] f'.ker :=
    LinearMap.codRestrict (f'.ker.restrictScalars ℚ) (cV.comp f.ker.subtype) (by
      intro x
      change f' (cV x.val) = 0
      have he := LinearMap.congr_fun hcomm x.val
      have hx : f x.val = 0 := x.property
      simpa only [LinearMap.comp_apply, hx, map_zero,
        LinearMap.restrictScalars_apply] using he.symm)
  have hbase : IsBaseChange ℝ k :=
    IsBaseChange.of_left_exact ℝ k cV cU (by ext x; rfl) hcomm hV hU
      f.exact_subtype_ker_map Subtype.val_injective
      f'.exact_subtype_ker_map Subtype.val_injective
  apply le_antisymm
  · intro x hx
    have H : (⟨x, hx⟩ : f'.ker).val ∈ Submodule.span ℝ (cV '' (f.ker : Set V)) := by
      induction (⟨x, hx⟩ : f'.ker) using hbase.inductionOn with
      | tmul v => exact Submodule.subset_span ⟨v.val, v.property, rfl⟩
      | smul a v hv => exact Submodule.smul_mem _ a hv
      | add v w hv hw => exact Submodule.add_mem _ hv hw
    exact H
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    change f' (cV v) = 0
    have he := LinearMap.congr_fun hcomm v
    have hv0 : f v = 0 := hv
    simpa only [LinearMap.comp_apply, hv0, map_zero,
      LinearMap.restrictScalars_apply] using he.symm

end Kernel

section Matrices

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise rational-to-real scalar extension for matrices. -/
def rationalMatrixCast : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℝ :=
  (Algebra.ofId ℚ ℝ).mapMatrix.toLinearMap

@[simp] lemma rationalMatrixCast_apply (M : Matrix ι ι ℚ) (i j : ι) :
    rationalMatrixCast M i j = (M i j : ℝ) := rfl

lemma rationalMatrixCast_isBaseChange : IsBaseChange ℝ (rationalMatrixCast (ι := ι)) := by
  change IsBaseChange ℝ (((Algebra.linearMap ℚ ℝ).compLeft ι).compLeft ι)
  exact IsBaseChange.finitePow ι (IsBaseChange.finitePow ι (IsBaseChange.linearMap ℚ ℝ))

/-- The equations for commuting with every member of a matrix family. -/
def commutatorFamily {K : Type*} [Field K] (B : κ → Matrix ι ι K) :
    Matrix ι ι K →ₗ[K] (κ → Matrix ι ι K) :=
  LinearMap.pi fun k => LinearMap.mulRight K (B k) - LinearMap.mulLeft K (B k)

@[simp] lemma commutatorFamily_apply {K : Type*} [Field K]
    (B : κ → Matrix ι ι K) (M : Matrix ι ι K) (k : κ) :
    commutatorFamily B M k = M * B k - B k * M := rfl

lemma mem_commutatorFamily_ker {K : Type*} [Field K]
    (B : κ → Matrix ι ι K) (M : Matrix ι ι K) :
    M ∈ (commutatorFamily B).ker ↔ ∀ k, Commute M (B k) := by
  change (fun k => M * B k - B k * M) = 0 ↔ _
  simp only [funext_iff, Pi.zero_apply, sub_eq_zero, commute_iff_eq]

variable [Finite κ]

/-- The exact rationality statement for a finite matrix centralizer. -/
theorem real_commutant_eq_span_rational (B : κ → Matrix ι ι ℚ) :
    (commutatorFamily (fun k => rationalMatrixCast (B k))).ker =
      Submodule.span ℝ
        (rationalMatrixCast '' ((commutatorFamily B).ker : Set (Matrix ι ι ℚ))) := by
  apply kernel_spanned_of_baseChange (commutatorFamily B)
    (commutatorFamily fun k => rationalMatrixCast (B k))
    rationalMatrixCast (rationalMatrixCast.compLeft κ)
    rationalMatrixCast_isBaseChange
    (IsBaseChange.finitePow κ rationalMatrixCast_isBaseChange)
  apply LinearMap.ext
  intro M
  funext k
  change (Algebra.ofId ℚ ℝ).mapMatrix (M * B k - B k * M) =
    (Algebra.ofId ℚ ℝ).mapMatrix M * (Algebra.ofId ℚ ℝ).mapMatrix (B k) -
      (Algebra.ofId ℚ ℝ).mapMatrix (B k) * (Algebra.ofId ℚ ℝ).mapMatrix M
  simp only [map_sub, map_mul]

/-- Every real matrix commuting with the given rational matrices is a
real linear combination of rational matrices with the same property. -/
theorem mem_span_rational_commutant (B : κ → Matrix ι ι ℚ)
    (M : Matrix ι ι ℝ) (hM : ∀ k, Commute M (rationalMatrixCast (B k))) :
    M ∈ Submodule.span ℝ
      (rationalMatrixCast '' ((commutatorFamily B).ker : Set (Matrix ι ι ℚ))) := by
  rw [← real_commutant_eq_span_rational]
  exact (mem_commutatorFamily_ker _ _).mpr hM

end Matrices

end DukePrimeDegree

end

end OAI
