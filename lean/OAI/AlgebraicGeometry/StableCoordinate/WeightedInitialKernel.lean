import OAI.AlgebraicGeometry.StableCoordinate.WeightedInitial
import Mathlib.RingTheory.Ideal.Operations

namespace OAI

/-!
# The homogeneous kernel criterion for a principal filtered quotient

A homogeneous polynomial disappears in the associated graded quotient by `(H)`
exactly when it is divisible by the highest component of `H`. The statement is
expressed in terms of representatives of lower weight; it thus supplies the
kernel computation independently of a particular associated-graded construction.
-/

namespace StableCoordinate
namespace WeightedInitial

open MvPolynomial

variable {σ K : Type*} [CommRing K] [IsDomain K]

omit [IsDomain K] in
lemma bounded_of_homogeneous {w : σ → ℤ} {p : MvPolynomial σ K} {d : ℤ}
    (hp : IsWeightedHomogeneous w p d) : Bounded w p d :=
  fun _ hm => (hp hm).le

omit [IsDomain K] in
lemma top_sub_lower {w : σ → ℤ} {p r : MvPolynomial σ K} {d : ℤ}
    (hp : IsWeightedHomogeneous w p d) (hr : Bounded w r (d - 1)) :
    weightedHomogeneousComponent w d (p - r) = p := by
  rw [map_sub, weightedHomogeneousComponent_eq_self hp,
    component_eq_zero_of_bounded hr (by omega), sub_zero]

/-- The homogeneous representative criterion for the kernel of the associated
-graded map from a weighted polynomial ring modulo one relation. -/
theorem homogeneous_quotient_kernel_iff
    (w : σ → ℤ) (H : MvPolynomial σ K) (e : ℤ)
    (hH : Bounded w H e) (hHt : weightedHomogeneousComponent w e H ≠ 0)
    {p : MvPolynomial σ K} {d : ℤ} (hp : IsWeightedHomogeneous w p d) :
    (∃ r : MvPolynomial σ K, Bounded w r (d - 1) ∧
      p - r ∈ Ideal.span ({H} : Set (MvPolynomial σ K))) ↔
    p ∈ Ideal.span ({weightedHomogeneousComponent w e H} : Set (MvPolynomial σ K)) := by
  classical
  by_cases hp0 : p = 0
  · subst p
    constructor
    · intro _
      exact Ideal.zero_mem _
    · intro _
      exact ⟨0, bounded_zero w _, by simp⟩
  constructor
  · rintro ⟨r, hr, hpr⟩
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hpr
    have hprtop : weightedHomogeneousComponent w d (p - r) ≠ 0 := by
      rw [top_sub_lower hp hr]
      exact hp0
    have hqr : q ≠ 0 := by
      intro hq0
      rw [hq0, mul_zero] at hq
      rw [hq, map_zero] at hprtop
      exact hprtop rfl
    obtain ⟨t, hqt, hqtop⟩ := exists_top (w := w) hqr
    obtain ⟨hprod, hprodtop⟩ := top_mul hH hqt hHt hqtop
    have hprbound : Bounded w (p - r) d :=
      (bounded_of_homogeneous hp).sub (hr.mono (by omega))
    have hde : d = e + t := by
      apply WithBot.coe_injective
      calc
        (d : WithBot ℤ) = weightedTotalDegree' w (p - r) :=
          (degree_eq_of_top hprbound hprtop).symm
        _ = weightedTotalDegree' w (H * q) := congrArg _ hq
        _ = ((e + t : ℤ) : WithBot ℤ) := degree_eq_of_top hprod hprodtop
    apply Ideal.mem_span_singleton.mpr
    refine ⟨weightedHomogeneousComponent w t q, ?_⟩
    calc
      p = weightedHomogeneousComponent w d (p - r) := (top_sub_lower hp hr).symm
      _ = weightedHomogeneousComponent w (e + t) (H * q) := by rw [hq, hde]
      _ = _ := component_mul_of_bounded hH hqt
  · intro hpmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hpmem
    have hq0 : q ≠ 0 := by
      intro hh
      rw [hh, mul_zero] at hq
      exact hp0 hq
    obtain ⟨t, hqt, hqtop⟩ := exists_top (w := w) hq0
    have hhom : IsWeightedHomogeneous w (weightedHomogeneousComponent w e H) e :=
      weightedHomogeneousComponent_isWeightedHomogeneous e H
    have htopself : weightedHomogeneousComponent w e
        (weightedHomogeneousComponent w e H) = weightedHomogeneousComponent w e H :=
      weightedHomogeneousComponent_eq_self hhom
    have htopself_ne : weightedHomogeneousComponent w e
        (weightedHomogeneousComponent w e H) ≠ 0 := by rwa [htopself]
    obtain ⟨hprod, hprodtop⟩ :=
      top_mul (bounded_of_homogeneous hhom) hqt htopself_ne hqtop
    have hde : d = e + t := by
      apply WithBot.coe_injective
      calc
        (d : WithBot ℤ) = weightedTotalDegree' w p :=
          (hp.weighted_total_degree hp0).symm
        _ = weightedTotalDegree' w (weightedHomogeneousComponent w e H * q) := congrArg _ hq
        _ = ((e + t : ℤ) : WithBot ℤ) := degree_eq_of_top hprod hprodtop
    have hptop : p = weightedHomogeneousComponent w e H * weightedHomogeneousComponent w t q := by
      calc
        p = weightedHomogeneousComponent w d p := (weightedHomogeneousComponent_eq_self hp).symm
        _ = weightedHomogeneousComponent w (e + t)
              (weightedHomogeneousComponent w e H * q) := by rw [hq, hde]
        _ = _ := by rw [component_mul_of_bounded (bounded_of_homogeneous hhom) hqt, htopself]
    let r := p - H * weightedHomogeneousComponent w t q
    refine ⟨r, ?_, ?_⟩
    · have hb := (bounded_sub_top hH).mul
        (bounded_of_homogeneous (weightedHomogeneousComponent_isWeightedHomogeneous t q))
      have hr : r = -((H - weightedHomogeneousComponent w e H) *
          weightedHomogeneousComponent w t q) := by
        dsimp [r]
        rw [hptop]
        ring
      rw [hr]
      have heq : e - 1 + t = d - 1 := by omega
      simpa only [heq] using hb.neg
    · apply Ideal.mem_span_singleton.mpr
      refine ⟨weightedHomogeneousComponent w t q, ?_⟩
      dsimp [r]
      ring

end WeightedInitial
end StableCoordinate

end OAI
