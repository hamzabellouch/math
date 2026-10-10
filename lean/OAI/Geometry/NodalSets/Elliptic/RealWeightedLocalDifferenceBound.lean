import OAI.Geometry.NodalSets.Elliptic.RealLocalWeakDifferenceQuadratic
import OAI.Geometry.NodalSets.Elliptic.RealLocalizedDifferenceIdentity

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_compact_global_multiplier_bound {n : ℕ} (eta : Coord n → ℝ)
    (he : Continuous eta) (hc : HasCompactSupport eta) :
    ∃ C > 0, ∀ u : Coord n → ℝ, MemLp u 2 volume →
      MemLp (fun x ↦ eta x*u x) 2 volume ∧
      (∫ x, (eta x*u x)^2) ≤ C*(∫ x, (u x)^2) := by
  obtain ⟨C,hC,hb⟩ := real_compact_multiplier_bound hc eta he
  refine ⟨C,hC,fun u hu ↦ ?_⟩
  refine ⟨real_compact_localL2_product hc eta u he Subset.rfl (hu.restrict _),?_⟩
  have hs : (∫ x, (eta x*u x)^2) = ∫ x in tsupport eta, (eta x*u x)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_pow (by decide)]
  rw [hs]
  exact (hb u (hu.restrict _)).2.trans (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hu.integrable_sq (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))) hC.le)

theorem real_weighted_local_difference_bound {n : ℕ} {Q : Set (Coord n)} (hQ : IsCompact Q)
    (eta chi : Coord n → ℝ) (he : Continuous eta) (hec : HasCompactSupport eta)
    (hc : ContDiff ℝ ∞ chi) (hs : tsupport chi ⊆ Q) (i : Fin n) :
    ∃ C > 0, ∀ (u g : Coord n → ℝ), MemLp u 2 (volume.restrict Q) →
      MemLp g 2 (volume.restrict Q) →
      (∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, u x*coordPartial psi x i)=-(∫ x in Q, g x*psi x)) →
      ∀ h : ℝ,
      (∀ x ∈ tsupport eta, x ∈ Q ∧ x+Pi.single i h ∈ Q ∧ chi x=1 ∧ chi (x+Pi.single i h)=1) →
      MemLp (fun x ↦ eta x*realDifferenceQuotient i h (Q.indicator u) x) 2 volume ∧
      (∫ x, (eta x*realDifferenceQuotient i h (Q.indicator u) x)^2) ≤
        C*((∫ x in Q, (u x)^2)+(∫ x in Q, (g x)^2)) := by
  obtain ⟨A,hA,ha⟩ := real_compact_global_multiplier_bound eta he hec
  obtain ⟨B,hB,hb⟩ := real_local_weak_difference_quadratic hQ chi hc hs i
  refine ⟨A*B,by positivity,fun u g hu hg hw h hend ↦ ?_⟩
  have hd := hb u g hu hg hw h
  have hm := ha _ hd.1
  have hid := real_supported_difference_localize Q u chi eta i h hend
  constructor
  · rw [hid]
    exact hm.1
  · change (∫ x, ((fun y ↦ eta y*realDifferenceQuotient i h (Q.indicator u) y) x)^2) ≤ _
    rw [hid]
    have ht := hm.2.trans (mul_le_mul_of_nonneg_left hd.2 hA.le)
    simpa only [← mul_assoc] using ht

end
end Yau

end OAI
