import Mathlib
import OAI.Probability.BinarySweep.Model
import OAI.Probability.BinarySweep.Representations.IsotypicProjectionMoment

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Fourier
open Representation Irrep Young

theorem young_trace_resolution {n : ℕ} (p : Equiv.Perm (Fin n) → ℂ) (q : ℕ) :
    evenMoment q (groupAverage (regular (Equiv.Perm (Fin n))) p)=
    ∑ℓ : n.Partition,(Module.finrank ℂ (PartitionHilbert ℓ):ℝ)*
      evenMoment q (groupAverage (partitionHilbertRep ℓ) p) := by
  let σ := regular (Equiv.Perm (Fin n))
  let B := ((groupAverage σ p).adjoint*groupAverage σ p)^q
  let S := fun ℓ : n.Partition => isotypicSpan (partitionHilbertRep ℓ) σ
  have hP : (∑ℓ : n.Partition,(S ℓ).starProjection.toLinearMap)=1 := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply,ContinuousLinearMap.coe_coe,Module.End.one_apply]
    exact partition_projection_sum σ (regular_unitary _) v
  have he (ℓ : n.Partition) :
      LinearMap.trace ℂ (RegularSpace (Equiv.Perm (Fin n)))
          (B*(S ℓ).starProjection.toLinearMap)=
        (Module.finrank ℂ (PartitionHilbert ℓ):ℂ)*
          LinearMap.trace ℂ (PartitionHilbert ℓ)
            (((groupAverage (partitionHilbertRep ℓ) p).adjoint*
              groupAverage (partitionHilbertRep ℓ) p)^q) := by
    have hc := even_compatible (partitionHilbertRep ℓ) σ p
      (partitionHilbertRep_unitary ℓ) (regular_unitary _) q
    rw [trace_mul_projection _ _ (isotypic_invariant_of_compatible _ _ _ _ hc),
      isotypic_trace _ _ _ _ hc,regular_multiplicity]
  unfold evenMoment
  change (LinearMap.trace ℂ _ B).re=_
  rw [←mul_one B,←hP,Finset.mul_sum,map_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [he]
  simp

theorem variation_fourier_bound {n : ℕ} (p q : Equiv.Perm (Fin n) → ℝ) :
    totalVariation p q ^2 ≤ (1/4:ℝ)*
      ∑ℓ : n.Partition,(Module.finrank ℂ (PartitionHilbert ℓ):ℝ)*
        evenMoment 1 (groupAverage (partitionHilbertRep ℓ) (fun g => (p g-q g:ℂ))) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun _ => (1:ℝ)) (fun g => |p g-q g|)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,sq_abs] at hc
  rw [←young_trace_resolution,regular_moment_one]
  simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  unfold totalVariation
  nlinarith

end BinaryCoordinateSweeps.Fourier

end

end OAI
