import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.CenterTrace
import OAI.Analysis.TracialCohomology.Expectations

namespace OAI

/-! Matrix norms for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices.System
open HochschildRigidity
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (s : PopaMatrices.System n (1:M))
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

lemma norm_sq_eq_trace (a : M) : ‖τ.toPreGNS a‖^2=(τ (star a*a)).re := by
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS,← Complex.ofReal_pow,Complex.ofReal_re]
    using congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS a))

include htr in
omit [StarOrderedRing M] in
lemma trace_diagonal_mul (i j : Fin n) (a : M) (ha : a ∈ s.commutant) :
    τ (s.entry i i*a)=τ (s.entry j j*a) := by
  calc
    τ (s.entry i i*a) = τ (s.entry i j*(s.entry j i*a)) := by rw [← mul_assoc,s.mul_entry,ite_eq_left rfl]
    _ = τ ((s.entry j i*a)*s.entry i j) := htr _ _
    _ = τ (s.entry j j*a) := by rw [mul_assoc,(ha i j).eq,← mul_assoc,s.mul_entry,ite_eq_left rfl]

include htr in
omit [StarOrderedRing M] in
lemma trace_diagonal (i : Fin n) (a : M) (ha : a ∈ s.commutant) :
    (n:ℂ)*τ (s.entry i i*a)=τ a := by
  calc
    (n:ℂ)*τ (s.entry i i*a) = ∑ j : Fin n, τ (s.entry j j*a) := by
      simp only [← s.trace_diagonal_mul τ htr i _ a ha,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ = τ a := by rw [← map_sum,← Finset.sum_mul,s.sum_diag,one_mul]

include htr in
lemma blocks_norm_sum (i0 : Fin n) (x : M) :
    (∑ i, ∑ j, ‖τ.toPreGNS (s.entry i0 i*x*s.entry j i0)‖^2)=‖τ.toPreGNS x‖^2 := by
  have hs : (∑ j, s.entry j i0*star (s.entry j i0))=1 := by
    simp only [s.star_entry,s.mul_entry,↓reduceIte,s.sum_diag]
  simp_rw [sum_preGNS_norm_mul_sq τ htr (fun j => s.entry j i0) hs]
  have hh := sum_preGNS_norm_mul_sq τ htr (fun i => s.entry i i0) hs (star x)
  simpa only [← preGNS_norm_star τ htr (star x*s.entry _ i0),star_mul,
    s.star_entry,star_star,preGNS_norm_star τ htr] using hh

omit [PartialOrder M] [StarOrderedRing M] in
lemma diagonal_sum_eq (i0 : Fin n) (x : M) :
    (∑ i, s.entry i0 i*x*s.entry i i0) = (n:ℝ) • (s.entry i0 i0*s.expect x) := by
  classical
  have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fin.pos i0))
  simp only [expect,mul_smul_comm,smul_smul,mul_inv_cancel₀ hn,one_smul,sumExpect,Finset.mul_sum]
  simp only [← mul_assoc,s.mul_entry,ite_mul,zero_mul]
  simp

include htr in
lemma diagonal_sum_norm (i0 : Fin n) (x : M) :
    ‖τ.toPreGNS (∑ i, s.entry i0 i*x*s.entry i i0)‖^2=
      (n:ℝ)*‖τ.toPreGNS (s.expect x)‖^2 := by
  let b := s.expect x
  have hb : b ∈ s.commutant := s.expect_mem x
  have htrace := congrArg Complex.re (s.trace_diagonal τ htr i0 (star b*b)
    (s.commutant.mul_mem (s.commutant.star_mem' hb) hb))
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at htrace
  rw [s.diagonal_sum_eq]
  rw [← Complex.coe_smul,map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg n),mul_pow,norm_sq_eq_trace]
  have he : star (s.entry i0 i0*b)*(s.entry i0 i0*b)=s.entry i0 i0*(star b*b) := by
    rw [star_mul,s.star_entry,mul_assoc,← mul_assoc (s.entry i0 i0),s.mul_entry,ite_eq_left rfl]
    rw [← mul_assoc,(s.commutant.star_mem' hb i0 i0).eq,mul_assoc]
  change (n:ℝ)^2*(τ (star (s.entry i0 i0*b)*(s.entry i0 i0*b))).re = _
  rw [he,norm_sq_eq_trace]
  change (n:ℝ)^2*(τ (s.entry i0 i0*(star b*b))).re=(n:ℝ)*(τ (star b*b)).re
  rw [← htrace]
  ring
end PopaMatrices.System

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma average_diagonal_mul {n : ℕ} (s : System n (1:M)) (i j : Fin n)
    (a : M) (ha : a ∈ s.commutant) :
    average e τ hτ htr hfaith (s.entry i i*a)=average e τ hτ htr hfaith (s.entry j j*a) := by
  calc
    _ = average e τ hτ htr hfaith (s.entry i j*(s.entry j i*a)) := by
      rw [←mul_assoc,s.mul_entry,ite_eq_left rfl]
    _ = average e τ hτ htr hfaith ((s.entry j i*a)*s.entry i j) := average_trace e τ hτ htr hfaith h1 _ _
    _ = _ := by rw [mul_assoc,(ha i j).eq,←mul_assoc,s.mul_entry,ite_eq_left rfl]

include h1 in
lemma average_diagonal {n : ℕ} (s : System n (1:M)) (i : Fin n)
    (a : M) (ha : a ∈ s.commutant) :
    (n:ℝ) • average e τ hτ htr hfaith (s.entry i i*a)=average e τ hτ htr hfaith a := by
  calc
    _ = ∑ j : Fin n, average e τ hτ htr hfaith (s.entry j j*a) := by
      simp only [←average_diagonal_mul e τ hτ htr hfaith h1 s i _ a ha,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_smul_eq_nsmul]
    _ = _ := by
      change (∑ j, expectation e τ hτ htr hfaith h1 (s.entry j j*a))=expectation e τ hτ htr hfaith h1 a
      rw [←map_sum,←Finset.sum_mul,s.sum_diag,one_mul]

include h1 in
lemma average_diagonal_one {n : ℕ} (s : System n (1:M)) (i : Fin n) :
    (n:ℝ) • average e τ hτ htr hfaith (s.entry i i)=1 := by
  simpa only [mul_one,average_id e τ hτ htr hfaith h1 (fun x => Commute.one_left x)] using
    average_diagonal e τ hτ htr hfaith h1 s i 1 s.commutant.one_mem

variable {n : ℕ}
def diagonal (s : System n (1:M)) (z : Fin n → M) : M := ∑ i, z i*s.entry i i

omit [PartialOrder M] [StarOrderedRing M] in
lemma diagonal_projection (s : System n (1:M)) (z : Fin n → M)
    (hz : ∀ i, IsStarProjection (z i)) (hc : ∀ i, Central (z i)) :
    IsStarProjection (diagonal s z) := by
  classical
  have h (i j : Fin n) : (z i*s.entry i i)*(z j*s.entry j j)=if i=j then z i*s.entry i i else 0 := by
    rw [mul_assoc,←mul_assoc (s.entry i i),(hc j _).eq.symm,mul_assoc (z j),s.mul_entry]
    by_cases hij : i=j
    · subst j; simp only [↓reduceIte,←mul_assoc, (hz i).isIdempotentElem.eq]
    · simp only [ite_eq_right hij,mul_zero]
  refine ⟨?_,?_⟩
  · change (∑ i, z i*s.entry i i)*(∑ i, z i*s.entry i i)=∑ i, z i*s.entry i i
    simp only [Finset.sum_mul,Finset.mul_sum,h]
    simp
  · change star (∑ i, z i*s.entry i i)=∑ i, z i*s.entry i i
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ((hz i).mul (s.diagonal_projection i) (hc i _)).isSelfAdjoint.star_eq

omit [PartialOrder M] [StarOrderedRing M] in
lemma diagonal_commutes (s : System n (1:M)) (z : Fin n → M)
    (hc : ∀ i, Central (z i)) (a : M) (ha : a ∈ s.commutant) :
    Commute a (diagonal s z) := by
  apply Commute.sum_right
  intro i _
  exact (hc i a).symm.mul_right (ha i i)

include h1 in
lemma average_diagonal_sum (s : System n (1:M)) (z : Fin n → M)
    (hc : ∀ i, Central (z i)) :
    (n:ℝ) • average e τ hτ htr hfaith (diagonal s z)=∑ i, z i := by
  change (n:ℝ) • expectation e τ hτ htr hfaith h1 (∑ i, z i*s.entry i i)=_
  rw [map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (n:ℝ) • average e τ hτ htr hfaith (z i*s.entry i i)=z i
  rw [average_bimodule e τ hτ htr hfaith h1 (hc i),←mul_smul_comm,
    average_diagonal_one e τ hτ htr hfaith h1,mul_one]
end PopaCenter

end

end OAI
