import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.AbelianComparison

namespace OAI

/-! Diagonal matrix projections and the type-II condition. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildMatrixSystems
open BoundedHochschild HochschildComparison HochschildTypeII FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

namespace MatrixSystem
variable {n : ℕ} (E : MatrixSystem M n)
omit [PartialOrder M] [StarOrderedRing M] in
lemma diagonal_projection (i : Fin n) : IsStarProjection (E.entry i i) :=
  ⟨by change E.entry i i*E.entry i i=E.entry i i; simp only [E.entry_mul,ite_true],E.star_entry i i⟩

omit [StarOrderedRing M] in
include htr in
lemma diagonal_trace (i j : Fin n) : τ (E.entry i i)=τ (E.entry j j) := by
  have ht := htr (E.entry i j) (E.entry j i)
  simpa only [E.entry_mul,ite_true] using ht

omit [StarOrderedRing M] in
include htr in
lemma mul_diagonal_trace (i : Fin n) : (n:ℝ)*(τ (E.entry i i)).re=(τ 1).re := by
  have hh := congrArg (fun x : M => (τ x).re) E.sum_diagonal
  rw [map_sum,Complex.re_sum] at hh
  simpa only [diagonal_trace τ htr E _ i,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] using hh

omit [PartialOrder M] [StarOrderedRing M] in
lemma diagonal_full (i : Fin n) (r : M) (hr : r ≠ 0) :
    ∃ a : M, E.entry i i*a*r ≠ 0 := by
  by_contra hn
  push Not at hn
  have her (j : Fin n) : E.entry i j*r=0 := by
    simpa only [E.entry_mul,ite_true] using hn (E.entry i j)
  have hrr (j : Fin n) : E.entry j j*r=0 := by
    calc
      E.entry j j*r = (E.entry j i*E.entry i j)*r := by rw [E.entry_mul,ite_eq_left rfl]
      _ = 0 := by rw [mul_assoc,her,mul_zero]
  apply hr
  calc
    r = (∑ j, E.entry j j)*r := by rw [E.sum_diagonal,one_mul]
    _ = 0 := by rw [Finset.sum_mul]; simp only [hrr,Finset.sum_const_zero]
end MatrixSystem

include e hτ htr hfaith in
lemma abelian_trace_bound {n : ℕ} (E : MatrixSystem M n) (i : Fin n)
    {p : M} (hp : AbelianProjection p) : (n:ℝ)*(τ p).re ≤ (τ 1).re := by
  have h := abelian_trace_le_full e τ hτ htr hfaith hp (E.diagonal_projection i)
    (fun r _hr hr0 => E.diagonal_full i r hr0)
  calc
    (n:ℝ)*(τ p).re ≤ (n:ℝ)*(τ (E.entry i i)).re :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
    _ = (τ 1).re := E.mul_diagonal_trace τ htr i

include e hτ htr hfaith in

lemma no_abelian_of_matrixSystems (hE : ∀ n : ℕ, Nonempty (MatrixSystem M (n+1)))
    {p : M} (hp : AbelianProjection p) : p=0 := by
  have hnonneg : 0 ≤ (τ p).re := (Complex.nonneg_iff.mp (τ.map_nonneg hp.1.nonneg)).1
  have hzero : (τ p).re=0 := by
    apply le_antisymm _ hnonneg
    by_contra hn
    have hpos : 0 < (τ p).re := lt_of_not_ge hn
    obtain ⟨n,hn⟩ := exists_nat_gt ((τ 1).re/(τ p).re)
    let E := Classical.choice (hE n)
    have hb := abelian_trace_bound e τ hτ htr hfaith E (0 : Fin (n+1)) hp
    have ht : (τ 1).re < (n:ℝ)*(τ p).re := (div_lt_iff₀ hpos).mp hn
    rw [Nat.cast_add,Nat.cast_one] at hb
    nlinarith
  apply hfaith p
  rw [hp.1.isSelfAdjoint.star_eq,hp.1.isIdempotentElem.eq]
  apply Complex.ext
  · exact hzero
  · exact (Complex.nonneg_iff.mp (τ.map_nonneg hp.1.nonneg)).2.symm

omit [StarOrderedRing M] in
include htr hfaith in
lemma finite_of_faithful_trace (a : M) (ha : star a*a=1) : a*star a=1 := by
  have hproj : IsStarProjection (a*star a) := by
    constructor
    · change (a*star a)*(a*star a)=a*star a
      simp only [mul_assoc,← mul_assoc (star a) a,ha,one_mul]
    · simp only [IsSelfAdjoint,star_mul,star_star]
  have hres := hproj.one_sub
  have ht : τ (1-a*star a)=0 := by rw [map_sub,htr a (star a),ha,sub_self]
  have hz := hfaith (1-a*star a) (by simpa only [hres.isSelfAdjoint.star_eq,
    hres.isIdempotentElem.eq] using ht)
  exact (sub_eq_zero.mp hz).symm

include e hτ htr hfaith in
theorem typeII1_of_matrixSystems (hE : ∀ n : ℕ, Nonempty (MatrixSystem M (n+1))) :
    TypeII1 M := by
  refine ⟨finite_of_faithful_trace τ htr hfaith,?_⟩
  intro z hz
  by_contra hz0
  obtain ⟨p,hp,_hpz,hp0⟩ := hz.2 z hz.1 le_rfl hz0
  exact hp0 (no_abelian_of_matrixSystems e τ hτ htr hfaith hE hp)

end HochschildMatrixSystems

end

end OAI
