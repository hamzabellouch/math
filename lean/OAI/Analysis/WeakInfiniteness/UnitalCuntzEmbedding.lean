import Mathlib
import OAI.Analysis.WeakInfiniteness.OInfinityMap
import OAI.Analysis.WeakInfiniteness.OrthogonalCores
import OAI.Analysis.WeakInfiniteness.UniverseIndividualInfiniteness

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma spectralRamp_one : cfcₙ (spectralRamp (1/4)) (1:A) = 1 := by
  rw [cfcₙ_eq_cfc (continuous_spectralRamp _).continuousOn
    (spectralRamp_eq_zero (by norm_num : (0:ℝ)<1/4) (by norm_num))]
  have h := cfc_algebraMap (A := A) (1:ℝ) (spectralRamp (1/4))
  rw [map_one,spectralRamp_eq_one (by norm_num : (0:ℝ)<1/4) (by norm_num),map_one] at h
  exact h

lemma exists_two_isometries_of_properlyInfinite
    (hpi : ProperlyInfinite (diagonalCopies 1 (1:A))) :
    ∃ r s : A,star r*r=1 ∧ star s*s=1 ∧ star r*s=0 := by
  obtain ⟨r,s,hr,hs,hrs,_⟩ := exists_two_exact_core_columns
    (show (0:A)≤1 from zero_le_one) hpi (by norm_num : (0:ℝ)<1/4)
  rw [spectralRamp_one] at hr hs
  exact ⟨r,s,hr,hs,hrs⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma star_pow_mul_pow_of_isometry {r : A} (hr : star r*r=1) (n : ℕ) :
    star (r^n)*r^n=1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      star (r^(n+1))*r^(n+1) = star r*(star (r^n)*r^n)*r := by
        simp only [pow_succ,star_mul,mul_assoc]
      _ = 1 := by rw [ih,mul_one,hr]

omit [PartialOrder A] [StarOrderedRing A] in
lemma star_mul_power_of_orthogonal {r s : A} (hrs : star r*s=0) {n : ℕ} (hn : n≠0) :
    star r*s^n=0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ',← mul_assoc,hrs,zero_mul]

omit [PartialOrder A] [StarOrderedRing A] in
lemma binaryCuntzFamily_relations {r s : A}
    (hr : star r*r=1) (hs : star s*s=1) (hrs : star r*s=0) (i j : ℕ) :
    star (s^i*r)*(s^j*r)=if i=j then 1 else 0 := by
  have hlt : ∀ i j : ℕ,i<j → star (s^i*r)*(s^j*r)=0 := by
    intro i j hij
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_lt hij
    have hk' : j=i+(k+1) := by omega
    calc
      star (s^i*r)*(s^j*r) = star r*(star (s^i)*s^i)*s^(k+1)*r := by
        rw [hk',pow_add,star_mul]
        simp only [mul_assoc]
      _ = 0 := by
        rw [star_pow_mul_pow_of_isometry hs,mul_one,
          star_mul_power_of_orthogonal hrs (Nat.succ_ne_zero k),zero_mul]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl]
    calc
      star (s^i*r)*(s^i*r) = star r*(star (s^i)*s^i)*r := by
        simp only [star_mul,mul_assoc]
      _ = 1 := by rw [star_pow_mul_pow_of_isometry hs,mul_one,hr]
  · rw [ite_eq_right hij]
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hlt i j hij
    · have h := congrArg star (hlt j i hji)
      simpa only [star_mul,star_star,star_zero] using h

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_commutator_of_cuntz_isometries [Nontrivial A] {r s : A}
    (hr : star r*r=1) (hs : star s*s=1) (hrs : star r*s=0) :
    ‖r*s-s*r‖=Real.sqrt 2 := by
  have hsr : star s*r=0 := by
    simpa only [star_mul,star_star,star_zero] using congrArg star hrs
  have hproduct : star (r*s-s*r)*(r*s-s*r) = (2:ℂ) • (1:A) := by
    calc
      star (r*s-s*r)*(r*s-s*r) =
          star s*(star r*r)*s - star s*(star r*s)*r -
            star r*(star s*r)*s + star r*(star s*s)*r := by
        simp only [star_sub,star_mul]
        noncomm_ring
      _ = (2:ℂ) • (1:A) := by
        rw [hr,hrs,hsr,hs]
        simp only [mul_one,mul_zero,zero_mul,sub_zero,hs,hr,two_smul]
  have hn : ‖r*s-s*r‖^2=2 := by
    rw [pow_two,← CStarRing.norm_star_mul_self,hproduct,norm_smul,norm_one,mul_one]
    norm_num
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  nlinarith [norm_nonneg (r*s-s*r),Real.sqrt_nonneg (2:ℝ)]

theorem exists_oInfinityHom_of_exact_weaklyPurelyInfinite (hA : Exact A) (hW : WeaklyPurelyInfinite A) :
    Nonempty (OInfinity →⋆ₐ[ℂ] A) := by
  obtain ⟨r,s,hr,hs,hrs⟩ := exists_two_isometries_of_properlyInfinite
    (exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any hA hW zero_le_one)
  exact ⟨oInfinityMap (fun n => s^n*r) (binaryCuntzFamily_relations hr hs hrs)⟩

end

end WeakPureInfiniteness
end

end OAI
