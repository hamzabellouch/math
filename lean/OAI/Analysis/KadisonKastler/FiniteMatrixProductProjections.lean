import OAI.Analysis.KadisonKastler.FiniteMatrixPartitions
import OAI.Analysis.KadisonKastler.FiniteBlockTraceLimit
import OAI.Analysis.KadisonKastler.TracialSequenceQuotient
import OAI.Analysis.KadisonKastler.OrthogonalIdempotentIndependence

namespace OAI

/-! # Nonzero orthogonal blocks in the finite-matrix tracial quotient -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

variable (n : ℕ) [NeZero n] (ω : Ultrafilter ℕ)

def finiteProductBlockSequence {k : ℕ} (i : Fin k) :
    VaryingBoundedSequence (FiniteMatrixModel n) :=
  ⟨fun j => finiteBlockProjection n j (finiteBlockSet i),
    memℓp_infty ⟨1, by rintro _ ⟨j, rfl⟩; exact finiteBlockProjection_norm_le n j _⟩⟩

def finiteProductBlock {k : ℕ} (i : Fin k) :
    TracialSequenceQuotient (finiteMatrixModelTrace n) ω :=
  tracialSequenceQuotientMap (finiteMatrixModelTrace n) ω (finiteProductBlockSequence n i)

theorem finiteProductBlockSequence_isProjection {k : ℕ} (i : Fin k) :
    IsStarProjection (finiteProductBlockSequence n i) := by
  constructor
  · apply Subtype.ext
    funext j
    exact (finiteBlockProjection_isProjection n j _).isIdempotentElem.eq
  · apply Subtype.ext
    funext j
    exact (finiteBlockProjection_isProjection n j _).isSelfAdjoint.star_eq

theorem finiteProductBlock_isProjection {k : ℕ} (i : Fin k) :
    IsStarProjection (finiteProductBlock n ω i) :=
  (finiteProductBlockSequence_isProjection n i).map
    (tracialSequenceQuotientMap (finiteMatrixModelTrace n) ω)

theorem finiteProductBlock_mul_of_ne {k : ℕ} (i j : Fin k) (hij : i ≠ j) :
    finiteProductBlock n ω i * finiteProductBlock n ω j = 0 := by
  change tracialSequenceQuotientMap (finiteMatrixModelTrace n) ω _ *
    tracialSequenceQuotientMap (finiteMatrixModelTrace n) ω _ = 0
  rw [← map_mul]
  have he : finiteProductBlockSequence n i * finiteProductBlockSequence n j = 0 := by
    apply Subtype.ext
    funext r
    exact finiteBlockProjection_mul_of_disjoint n r _ _ (finiteBlockSet_disjoint i j hij)
  rw [he, map_zero]

theorem finiteProductBlock_trace (hω : (ω : Filter ℕ) ≤ atTop) {k : ℕ} (i : Fin k) :
    (tracialQuotientTrace (finiteMatrixModelTrace n) ω).toLinearMap (finiteProductBlock n ω i) =
      (k : ℂ)⁻¹ := by
  have hquot := tracialQuotientTrace_limit (finiteMatrixModelTrace n) ω (finiteProductBlockSequence n i)
  have hk : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hreal := (tendsto_finiteBlock_ratio k hk).mono_left hω
  have hcomplex := (Complex.continuous_ofReal.tendsto _).comp hreal
  have hlim : Tendsto (fun j => (finiteMatrixModelTrace n j).toLinearMap
      (finiteProductBlockSequence n i j)) (ω : Filter ℕ) (𝓝 (k : ℂ)⁻¹) := by
    simpa only [finiteProductBlockSequence, finiteBlockProjection_trace, finiteBlockSet_card,
      Function.comp_def, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast,
      one_div, Nat.cast_add, Nat.cast_one, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_add, mul_one, div_eq_mul_inv, mul_comm] using hcomplex
  exact tendsto_nhds_unique hquot hlim

theorem finiteProductBlock_ne_zero (hω : (ω : Filter ℕ) ≤ atTop) {k : ℕ} (i : Fin k) :
    finiteProductBlock n ω i ≠ 0 := by
  intro hz
  have h := finiteProductBlock_trace n ω hω i
  rw [hz, map_zero] at h
  exact (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)))) h.symm

theorem finiteMatrixTracialQuotient_infinite (hω : (ω : Filter ℕ) ≤ atTop) :
    ¬ FiniteDimensional ℂ (TracialSequenceQuotient (finiteMatrixModelTrace n) ω) := by
  intro hdim
  let := hdim
  let d := Module.finrank ℂ (TracialSequenceQuotient (finiteMatrixModelTrace n) ω)
  have hli : LinearIndependent ℂ (fun i : Fin (d + 1) => finiteProductBlock n ω i) := by
    apply linearIndependent_of_orthogonal_idempotents _ (finiteProductBlock_ne_zero n ω hω)
    intro i j
    by_cases h : i = j
    · subst j
      simpa only [ite_true] using (finiteProductBlock_isProjection n ω i).isIdempotentElem.eq
    · simpa only [h, ite_false] using finiteProductBlock_mul_of_ne n ω i j h
  have hh := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hh
  change d + 1 ≤ d at hh
  omega

end

end KadisonKastler

end OAI
