import OAI.Analysis.KadisonKastler.CentralSupportCover
import OAI.Analysis.KadisonKastler.ProjectionMatrices
import OAI.Analysis.KadisonKastler.RowRepresentationContraction

namespace OAI

/-! Normalized finite rows from an orthogonal family of partial isometries.
The missing initial projection is included as one extra row entry. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def finiteSupportSum (s : Finset (PartialIsometry M)) : Algebra M :=
  ∑ v ∈ s, v.support.val

theorem finiteSupportSum_projection (s : Finset (PartialIsometry M))
    (ho : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → v.support.val * w.support.val = 0) :
    IsStarProjection (finiteSupportSum s) :=
  isStarProjection_sum_orthogonal s (fun v => v.support.val)
    (fun v _ => v.support.property) ho

theorem finiteSupportSum_mul_member (s : Finset (PartialIsometry M))
    (ho : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → v.support.val * w.support.val = 0)
    (v : PartialIsometry M) (hv : v ∈ s) :
    finiteSupportSum s * v.support.val = v.support.val := by
  classical
  rw [finiteSupportSum, Finset.sum_mul, Finset.sum_eq_single v]
  · exact v.support.property.isIdempotentElem.eq
  · intro w hw hwv
    exact ho w hw v hv hwv
  · exact fun h => (h hv).elim

theorem finiteSupportSum_mul_of_subset (s t : Finset (PartialIsometry M))
    (ho : ∀ v ∈ t, ∀ w ∈ t, v ≠ w → v.support.val * w.support.val = 0)
    (hst : s ⊆ t) : finiteSupportSum t * finiteSupportSum s = finiteSupportSum s := by
  simp only [finiteSupportSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact finiteSupportSum_mul_member t ho v (hst hv)

def finiteSupportRow (s : Finset (PartialIsometry M)) : Option s → Algebra M
  | none => 1 - finiteSupportSum s
  | some v => star v.val.val

theorem finiteSupportRow_normalized (s : Finset (PartialIsometry M))
    (ho : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → v.support.val * w.support.val = 0) :
    ∑ i, finiteSupportRow s i * star (finiteSupportRow s i) = 1 := by
  classical
  have hp := finiteSupportSum_projection s ho
  rw [Fintype.sum_option]
  simp only [finiteSupportRow, star_sub, star_one, hp.isSelfAdjoint.star_eq, star_star]
  have hs : ∑ v : s, star v.val.val * v.val.val = finiteSupportSum s := by
    simp only [PartialIsometry.initial]
    exact Finset.sum_coe_sort s (fun v => v.support.val)
  rw [hs, (hp.one_sub).isIdempotentElem.eq]
  abel

theorem partialIsometry_mul_finiteSupportSum (s : Finset (PartialIsometry M))
    (ho : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → v.support.val * w.support.val = 0)
    (v : PartialIsometry M) (hv : v ∈ s) : v.val * finiteSupportSum s = v.val := by
  have h := finiteSupportSum_mul_member s ho v hv
  have hs : v.support.val * finiteSupportSum s = v.support.val := by
    simpa only [star_mul, (finiteSupportSum_projection s ho).isSelfAdjoint.star_eq,
      v.support.property.isSelfAdjoint.star_eq] using congrArg star h
  calc
    _ = (v.val * v.support.val) * finiteSupportSum s := by rw [v.mul_support]
    _ = v.val := by rw [mul_assoc, hs, v.mul_support]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem finiteSupportRow_diagonal_compression
    (e : AlgebraProjection M) (s : Finset (PartialIsometry M))
    (ho : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → v.support.val * w.support.val = 0)
    (he : ∀ v ∈ s, v.target ≤ e)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : H →L[ℂ] K) :
    (representationRowAverage π (finiteSupportRow s) R).comp
        (finiteSupportSum s : H →L[ℂ] H) =
      (representationRowAverage π (finiteSupportRow s)
        ((π e.val).comp (R.comp (e.val : H →L[ℂ] H)))).comp
          (finiteSupportSum s : H →L[ℂ] H) := by
  classical
  have hp := finiteSupportSum_projection s ho
  have hzero : (1 - finiteSupportSum s) * finiteSupportSum s = 0 := by
    rw [sub_mul, one_mul, hp.isIdempotentElem.eq, sub_self]
  have hev (v : s) : e.val * v.val.val = v.val.val := by
    calc
      _ = e.val * (v.val.target.val * v.val.val) := by rw [v.val.target_mul]
      _ = v.val.val := by rw [← mul_assoc, he v.val v.property, v.val.target_mul]
  have hve (v : s) : star v.val.val * e.val = star v.val.val := by
    simpa only [star_mul, e.property.isSelfAdjoint.star_eq] using congrArg star (hev v)
  ext ξ
  simp only [representationRowAverage, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  change π (finiteSupportRow s i)
      (R (((star (finiteSupportRow s i) : Algebra M) : H →L[ℂ] H)
        ((finiteSupportSum s : H →L[ℂ] H) ξ))) =
    π (finiteSupportRow s i) (π e.val (R ((e.val : H →L[ℂ] H)
      (((star (finiteSupportRow s i) : Algebra M) : H →L[ℂ] H)
        ((finiteSupportSum s : H →L[ℂ] H) ξ)))))
  cases i with
  | none =>
      have hz : ((star (finiteSupportRow s none) : Algebra M) : H →L[ℂ] H)
          ((finiteSupportSum s : H →L[ℂ] H) ξ) = 0 := by
        have h := congrArg (fun a : Algebra M => (a : H →L[ℂ] H) ξ) hzero
        simpa only [finiteSupportRow, star_sub, star_one, hp.isSelfAdjoint.star_eq,
          MulMemClass.coe_mul, mul_apply_eq_comp, ZeroMemClass.coe_zero, zero_apply] using h
      simp only [hz, map_zero]
  | some v =>
      have hsp := partialIsometry_mul_finiteSupportSum s ho v.val v.property
      have hvξ : ((star (finiteSupportRow s (some v)) : Algebra M) : H →L[ℂ] H)
          ((finiteSupportSum s : H →L[ℂ] H) ξ) = (v.val.val : H →L[ℂ] H) ξ := by
        simpa only [finiteSupportRow, star_star, MulMemClass.coe_mul, mul_apply_eq_comp] using
          congrArg (fun a : Algebra M => (a : H →L[ℂ] H) ξ) hsp
      rw [hvξ]
      have heξ : (e.val : H →L[ℂ] H) ((v.val.val : H →L[ℂ] H) ξ) =
          (v.val.val : H →L[ℂ] H) ξ :=
        congrArg (fun a : Algebra M => (a : H →L[ℂ] H) ξ) (hev v)
      change _ = π (star v.val.val) (π e.val (R ((e.val : H →L[ℂ] H)
        ((v.val.val : H →L[ℂ] H) ξ))))
      rw [heξ]
      have hπ : π (star v.val.val) * π e.val = π (star v.val.val) := by
        rw [← map_mul, hve]
      exact (congrArg (fun A : K →L[ℂ] K => A (R ((v.val.val : H →L[ℂ] H) ξ))) hπ).symm

theorem finiteSupportRow_localized_norm_le
    (e : AlgebraProjection M) (s : Finset (PartialIsometry M))
    (ho : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → v.support.val * w.support.val = 0)
    (he : ∀ v ∈ s, v.target ≤ e)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : H →L[ℂ] K) :
    ‖(representationRowAverage π (finiteSupportRow s) R).comp
      (finiteSupportSum s : H →L[ℂ] H)‖ ≤
      ‖(π e.val).comp (R.comp (e.val : H →L[ℂ] H))‖ := by
  rw [finiteSupportRow_diagonal_compression e s ho he π R]
  have hp := (finiteSupportSum_projection s ho).map M.toStarSubalgebra.subtype
  have hb := (representationRowAverage π (finiteSupportRow s)
    ((π e.val).comp (R.comp (e.val : H →L[ℂ] H)))).opNorm_comp_le
      (finiteSupportSum s : H →L[ℂ] H)
  have hr := representationRowAverage_norm_le π (finiteSupportRow s)
    (finiteSupportRow_normalized s ho) ((π e.val).comp (R.comp (e.val : H →L[ℂ] H)))
  exact hb.trans ((mul_le_mul_of_nonneg_left hp.norm_le (norm_nonneg _)).trans
    (by simpa only [mul_one] using hr))

end

end KadisonKastler

end OAI
