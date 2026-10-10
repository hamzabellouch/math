import OAI.Analysis.Nuclearity.PositiveConeSeparation
import OAI.Analysis.Nuclearity.PositiveFunctionalKernel

namespace OAI

/-! The positive-cone criterion in KR02, Lemma 7.17(ii).
The hypothesis records closure under actual coefficient conjugation.
The conclusion is membership in the cone, not an absorption assumption. -/

noncomputable section
open scoped Topology ComplexOrder

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Conjugation on the real self-adjoint part. -/
def selfAdjointConjugation (d : A) : selfAdjoint A →L[ℝ] selfAdjoint A :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨star d * (a : A) * d, a.property.conjugate' d⟩
      map_add' := by intro a b; ext; simp [mul_add, add_mul]
      map_smul' := by intro c a; ext; simp [mul_smul_comm, smul_mul_assoc] }
    (‖d‖ * ‖d‖) (by
      intro a
      change ‖star d * (a : A) * d‖ ≤ (‖d‖ * ‖d‖) * ‖a‖
      calc
        _ ≤ (‖star d‖ * ‖(a : A)‖) * ‖d‖ :=
          (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ = _ := by
          change (‖star d‖ * ‖(a : A)‖) * ‖d‖ = (‖d‖ * ‖d‖) * ‖(a : A)‖
          rw [norm_star]
          ring)

@[simp] lemma selfAdjointConjugation_apply (d : A) (a : selfAdjoint A) :
    (selfAdjointConjugation d a : A) = star d * (a : A) * d := rfl

def conjugateRealFunctional (φ : WeakDual ℝ (selfAdjoint A)) (d : A) :
    WeakDual ℝ (selfAdjoint A) :=
  StrongDual.toWeakDual ((WeakDual.toStrongDual φ).comp (selfAdjointConjugation d))

@[simp] lemma conjugateRealFunctional_apply (φ : WeakDual ℝ (selfAdjoint A))
    (d : A) (a : selfAdjoint A) :
    conjugateRealFunctional φ d a = φ (selfAdjointConjugation d a) := rfl

variable [PartialOrder A] [StarOrderedRing A]

/-- The negative part produces an explicit negative square by conjugation. -/
lemma sqrt_negPart_conjugation (a : selfAdjoint A) :
    star (CFC.sqrt (a : A)⁻) * (a : A) * CFC.sqrt (a : A)⁻ =
      -((a : A)⁻ * (a : A)⁻) := by
  let p : A := (a : A)⁺
  let n : A := (a : A)⁻
  let d : A := CFC.sqrt n
  have hp : IsSelfAdjoint p := (CFC.posPart_nonneg (a : A)).isSelfAdjoint
  have hn : IsSelfAdjoint n := (CFC.negPart_nonneg (a : A)).isSelfAdjoint
  have hd : IsSelfAdjoint d := (CFC.sqrt_nonneg n).isSelfAdjoint
  have hdd : d * d = n := CFC.sqrt_mul_sqrt_self n
  have hpn : p * n = 0 := CFC.posPart_mul_negPart (a : A)
  have hpd : p * d = 0 := by
    apply (CStarRing.mul_star_self_eq_zero_iff (p * d)).mp
    calc
      (p * d) * star (p * d) = p * (d * d) * p := by
        simp only [star_mul, hd.star_eq, hp.star_eq, mul_assoc]
      _ = 0 := by rw [hdd, hpn, zero_mul]
  have hdp : d * p = 0 := by
    simpa only [star_mul, hd.star_eq, hp.star_eq, star_zero] using congrArg star hpd
  have ha : (a : A) = p - n := (CFC.posPart_sub_negPart (a : A) a.property).symm
  change star d * (a : A) * d = -(n * n)
  rw [hd.star_eq, ha, mul_sub, sub_mul, hdp, zero_mul, zero_sub]
  congr 1
  calc
    d * n * d = (d * d) * (d * d) := by rw [← hdd]; simp only [mul_assoc]
    _ = n * n := by rw [hdd]

/-- A closed positive cone stable under coefficient conjugation contains every
positive functional whose square nullspace contains its common square nullspace.
This is the precise functional-analytic step of KR02 Lemma 7.17(ii). -/
theorem mem_positive_cone_of_common_nullspace
    (K : Set (WeakDual ℝ (selfAdjoint A)))
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) (hzero : 0 ∈ K)
    (hscale : ∀ t : ℝ, 0 ≤ t → ∀ φ ∈ K, t • φ ∈ K)
    (hpositive : ∀ φ ∈ K, ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ φ a)
    (hconjugate : ∀ φ ∈ K, ∀ d : A, conjugateRealFunctional φ d ∈ K)
    (φ₀ : WeakDual ℝ (selfAdjoint A))
    (hφ₀ : ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ φ₀ a)
    (hnull : ∀ x : A,
      (∀ φ ∈ K, φ ⟨star x * x, IsSelfAdjoint.star_mul_self x⟩ = 0) →
      φ₀ ⟨star x * x, IsSelfAdjoint.star_mul_self x⟩ = 0) : φ₀ ∈ K := by
  by_contra hnot
  obtain ⟨a, ha, hsep⟩ :=
    selfAdjoint_separator_of_closed_cone K hclosed hconvex hzero hscale φ₀ hnot
  let n : selfAdjoint A := ⟨(a : A)⁻, (CFC.negPart_nonneg (a : A)).isSelfAdjoint⟩
  let p : selfAdjoint A := ⟨(a : A)⁺, (CFC.posPart_nonneg (a : A)).isSelfAdjoint⟩
  let q : selfAdjoint A := ⟨star (n : A) * (n : A), IsSelfAdjoint.star_mul_self _⟩
  have hq (φ : WeakDual ℝ (selfAdjoint A)) (hφ : φ ∈ K) : φ q = 0 := by
    have hnonneg := hpositive φ hφ q (star_mul_self_nonneg (n : A))
    have hnegative := hsep (conjugateRealFunctional φ (CFC.sqrt (n : A)))
      (hconjugate φ hφ _)
    have heq : selfAdjointConjugation (CFC.sqrt (n : A)) a = -q := by
      apply Subtype.ext
      change star (CFC.sqrt (a : A)⁻) * (a : A) * CFC.sqrt (a : A)⁻ =
        -(star ((a : A)⁻) * (a : A)⁻)
      rw [((CFC.negPart_nonneg (a : A)).isSelfAdjoint).star_eq]
      exact sqrt_negPart_conjugation a
    change 0 ≤ φ (selfAdjointConjugation (CFC.sqrt (n : A)) a) at hnegative
    rw [heq, map_neg] at hnegative
    linarith
  have hq₀ : φ₀ q = 0 := hnull (n : A) hq
  have hn₀ : φ₀ n = 0 := positiveRealFunctional_eq_zero_of_square
    (WeakDual.toStrongDual φ₀).toLinearMap hφ₀ n hq₀
  have hdecomp : a = p - n := by
    apply Subtype.ext
    exact (CFC.posPart_sub_negPart (a : A) a.property).symm
  have hp₀ : 0 ≤ φ₀ p := hφ₀ p (CFC.posPart_nonneg (a : A))
  rw [hdecomp, map_sub, hn₀, sub_zero] at ha
  exact (not_lt_of_ge hp₀) ha

end WeakPureInfiniteness

end

end OAI
