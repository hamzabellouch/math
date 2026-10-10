import Mathlib
import OAI.Analysis.BoundedHochschild.Catalan
import OAI.Analysis.BoundedHochschild.CollisionBounds

namespace OAI

/-! Newton polar polynomials and normalized free sums. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildNewtonPolar
noncomputable section
open Polynomial

 
def polarPoly : ℕ → ℝ[X]
  | 0 => C (1/2)
  | n+1 => C (1/2) * polarPoly n * (C 3-X*(polarPoly n)^2)

def defectPoly (n : ℕ) : ℝ[X] := 1-X*(polarPoly n)^2

lemma defect_succ (n : ℕ) :
    defectPoly (n+1) = C (1/4)*(defectPoly n)^2*(C 3+defectPoly n) := by
  apply Polynomial.funext
  intro t
  simp only [defectPoly,polarPoly,eval_sub,eval_one,eval_mul,eval_X,eval_pow,eval_C,eval_add]
  ring

lemma eval_defect_bounds (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht4 : t ≤ 4) :
    0 ≤ (defectPoly n).eval t ∧ (defectPoly n).eval t ≤ (1-t/4)^(n+1) := by
  have hc : 0 ≤ 1-t/4 := by linarith
  have hc1 : 1-t/4 ≤ 1 := by linarith
  induction n with
  | zero => simp only [defectPoly,polarPoly,eval_sub,eval_one,eval_mul,eval_X,eval_pow,eval_C]
            constructor <;> nlinarith
  | succ n ih =>
    have hpow : (1-t/4)^(n+1) ≤ 1-t/4 := by
      rw [pow_succ]
      exact mul_le_of_le_one_left hc (pow_le_one₀ hc hc1)
    have he1 : (defectPoly n).eval t ≤ 1 := (ih.2.trans hpow).trans hc1
    rw [defect_succ]
    simp only [eval_mul,eval_C,eval_pow,eval_add]
    constructor
    · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith [ih.1])
    · calc
        (1/4:ℝ)*(defectPoly n).eval t^2*(3+(defectPoly n).eval t) ≤
            (defectPoly n).eval t^2 := by nlinarith [sq_nonneg ((defectPoly n).eval t)]
        _ ≤ (1-t/4)^(n+1)*(1-t/4) := by
          rw [pow_two]
          exact mul_le_mul ih.2 (ih.2.trans hpow) ih.1 (pow_nonneg hc _)
        _ = _ := by rw [← pow_succ]

lemma eval_defect_le_one (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht4 : t ≤ 4) :
    (defectPoly n).eval t ≤ 1 :=
  (eval_defect_bounds n t ht ht4).2.trans (pow_le_one₀ (by linarith) (by linarith))

section Algebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

 
def polarApprox (s : A) (n : ℕ) : A := s * aeval (star s*s) (polarPoly n)

omit [PartialOrder A] [StarOrderedRing A] in
lemma aeval_selfAdjoint (a : A) (ha : IsSelfAdjoint a) (p : ℝ[X]) :
    IsSelfAdjoint (aeval a p) := by
  rw [← cfc_polynomial p a ha]
  exact cfc_predicate _ _

omit [PartialOrder A] [StarOrderedRing A] in
lemma polarApprox_defect (s : A) (n : ℕ) :
    1-star (polarApprox s n)*polarApprox s n = aeval (star s*s) (defectPoly n) := by
  let a := star s*s
  let p := aeval a (polarPoly n)
  have hp : star p = p := (aeval_selfAdjoint a (IsSelfAdjoint.star_mul_self s) _).star_eq
  have hcomm : Commute a p := by
    simpa only [aeval_X] using (Commute.all (X:ℝ[X]) (polarPoly n)).map (aeval a)
  simp only [polarApprox,star_mul]
  rw [mul_assoc (star (aeval (star s*s) (polarPoly n))), ← mul_assoc (star s)]
  change 1-star p*(a*p) = _
  rw [← mul_assoc,hp]
  simp only [defectPoly,map_sub,map_one,map_mul,aeval_X,map_pow]
  change 1-p*a*p = 1-a*p^2
  rw [hcomm.eq.symm,pow_two,mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
lemma spectrum_star_mul_bound [Nontrivial A] (s : A) (hs : ‖s‖ ≤ 2) {t : ℝ}
    (ht : t ∈ spectrum ℝ (star s*s)) : 0 ≤ t ∧ t ≤ 4 := by
  constructor
  · exact spectrum_star_mul_self_nonneg t ht
  · calc
      t ≤ |t| := le_abs_self t
      _ = ‖t‖ := (Real.norm_eq_abs t).symm
      _ ≤ ‖star s*s‖ := spectrum.norm_le_norm_of_mem ht
      _ ≤ 4 := by rw [CStarRing.norm_star_mul_self]; nlinarith [norm_nonneg s]

lemma defect_nonneg [Nontrivial A] (s : A) (hs : ‖s‖ ≤ 2) (n : ℕ) :
    0 ≤ 1-star (polarApprox s n)*polarApprox s n := by
  rw [polarApprox_defect,← cfc_polynomial _ _ (IsSelfAdjoint.star_mul_self s)]
  apply cfc_nonneg
  intro t ht
  obtain ⟨ht0,ht4⟩ := spectrum_star_mul_bound s hs ht
  exact (eval_defect_bounds n t ht0 ht4).1

lemma polarApprox_norm_le_one [Nontrivial A] (s : A) (hs : ‖s‖ ≤ 2) (n : ℕ) :
    ‖polarApprox s n‖ ≤ 1 := by
  have hd := defect_nonneg s hs n
  rw [sub_nonneg,← CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _),
    CStarRing.norm_star_mul_self] at hd
  nlinarith [norm_nonneg (polarApprox s n)]

lemma defect_le_cutoff [Nontrivial A] (s : A) (hs : ‖s‖ ≤ 2) (n : ℕ) :
    1-star (polarApprox s n)*polarApprox s n ≤ (1-(1/4:ℝ) • (star s*s))^(n+1) := by
  have he : (1-(1/4:ℝ) • (star s*s))^(n+1) =
      aeval (star s*s) (((1:ℝ[X])-C (1/4)*X)^(n+1)) := by simp [Algebra.smul_def]
  rw [polarApprox_defect,he,← cfc_polynomial _ _ (IsSelfAdjoint.star_mul_self s),
    ← cfc_polynomial _ _ (IsSelfAdjoint.star_mul_self s)]
  apply (cfc_le_iff _ _ _).mpr
  intro t ht
  obtain ⟨ht0,ht4⟩ := spectrum_star_mul_bound s hs ht
  simpa only [eval_pow,eval_sub,eval_one,eval_mul,eval_C,eval_X,div_eq_mul_inv,mul_comm,one_mul]
    using (eval_defect_bounds n t ht0 ht4).2

end Algebra
end
end HochschildNewtonPolar

namespace HochschildFreeSums
noncomputable section
open Finset Polynomial Filter Topology
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
 
def freeSum {α : Type*} [Fintype α] (u : FreeGroup α →* A) : A :=
  (Real.sqrt (Fintype.card α))⁻¹ • ∑ i, u (FreeGroup.of i)

lemma collisionCard_of_injective {I G : Type*} [Fintype I] [DecidableEq G]
    (g : I → G) (hg : Function.Injective g) :
    Fintype.card {p : I × I // g p.1 = g p.2} = Fintype.card I := by
  classical
  apply Fintype.card_congr
  exact {
    toFun := fun p => p.val.1
    invFun := fun i => ⟨(i,i),rfl⟩
    left_inv := fun p => Subtype.ext (Prod.ext rfl (hg p.property))
    right_inv := fun _ => rfl }

lemma norm_freeSum_le_two {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (τ : A →ₚ[ℂ] ℂ) (u : FreeGroup α →* A)
    (h1 : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
    (hfree : ∀ g, g ≠ 1 → τ (u g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0) : ‖freeSum u‖ ≤ 2 := by
  have hn := HochschildIndexedHaagerup.norm_sum_le τ u h1 hu hfree htr hf
    FreeGroup.of 1 (fun i => by simp)
  rw [collisionCard_of_injective _ FreeGroup.of_injective] at hn
  have hc : 0 < Real.sqrt (Fintype.card α) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  rw [freeSum,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
  calc
    _ ≤ (Real.sqrt (Fintype.card α))⁻¹ * ((1+1:ℝ)*Real.sqrt (Fintype.card α)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_one] using hn) (inv_nonneg.mpr hc.le)
    _ = 2 := by field_simp; ring

omit [PartialOrder A] [StarOrderedRing A] in
lemma star_mul_freeSum {α : Type*} [Fintype α] (u : FreeGroup α →* A) :
    star (freeSum u)*freeSum u = HochschildCatalanMoments.positiveSum u := by
  rw [freeSum,star_smul,star_trivial,smul_mul_smul]
  have hscalar : (Real.sqrt (Fintype.card α))⁻¹ * (Real.sqrt (Fintype.card α))⁻¹ =
      (Fintype.card α:ℝ)⁻¹ := by
    rw [← pow_two,inv_pow,Real.sq_sqrt (by positivity)]
  rw [hscalar]
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  change (Complex.ofReal ((Fintype.card α:ℝ)⁻¹)) • _ = _
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast,HochschildCatalanMoments.positiveSum]

 
def catalanFunctional : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun n => LinearMap.mulRight ℝ (catalan n : ℝ))

@[simp] lemma catalanFunctional_X_pow (n : ℕ) : catalanFunctional (X^n) = catalan n := by
  change (X^n:ℝ[X]).sum (fun n c => c*(catalan n:ℝ)) = _
  rw [← one_mul (X^n),← map_one C, C_mul_X_pow_eq_monomial, sum_monomial_index]
  · simp
  · simp

omit [StarOrderedRing A] in
lemma polynomial_moments_tendsto (τ : A →ₚ[ℂ] ℂ) (s : ℕ → A)
    (hm : ∀ n, Tendsto (fun r => (τ ((star (s r)*s r)^n)).re) atTop (nhds (catalan n:ℝ)))
    (p : ℝ[X]) : Tendsto (fun r => (τ (aeval (star (s r)*s r) p)).re)
      atTop (nhds (catalanFunctional p)) := by
  change Tendsto (fun r => HochschildCatalan.momentFunctional τ (star (s r)*s r) p) _ _
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial,← smul_eq_C_mul,map_smul]
    simp only [map_smul,HochschildCatalan.momentFunctional_X_pow,catalanFunctional_X_pow]
    exact (hm n).const_smul c

omit [StarOrderedRing A] in
lemma freeSum_moments_tendsto (τ : A →ₚ[ℂ] ℂ) (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
    (h1 : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
    (hfree : ∀ r g, g ≠ 1 → τ (u r g) = 0) (n : ℕ) :
    Tendsto (fun r => (τ ((star (freeSum (u r))*freeSum (u r))^n)).re)
      atTop (nhds (catalan n:ℝ)) := by
  have he (r : ℕ) : (τ ((star (freeSum (u r))*freeSum (u r))^n)).re =
      (Fintype.card (HochschildCatalanWords.ReturnWords (Fin (r+1)) n):ℝ) / ((r+1:ℕ):ℝ)^n := by
    rw [star_mul_freeSum]
    simpa only [PositiveLinearMap.coe_toLinearMap, Fintype.card_fin] using HochschildCatalanMoments.re_trace_positiveSum_pow (u r) (hu r) τ.toLinearMap h1 (hfree r) n
  simp_rw [he]
  exact (HochschildCatalanWords.normalized_returnWord_count_tendsto n).comp (tendsto_add_atTop_nat 1)

lemma cutoff_catalan_tendsto_zero : Tendsto
    (fun n => catalanFunctional (HochschildCatalan.cutoff^(n+1))) atTop (nhds 0) := by
  exact (HochschildCatalan.cutoff_moment_tendsto_zero catalanFunctional
    catalanFunctional_X_pow).comp (tendsto_add_atTop_nat 1)

end
end HochschildFreeSums
end

end OAI
