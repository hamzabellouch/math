import OAI.MeasureTheory.Falconer.Estimates.FiniteFamilyOverlap
import OAI.MeasureTheory.Falconer.Geometry.ScalarBallCandidates

namespace OAI

/-! Relative common-slice selection and loss bounds for deleting short
intervals of directions. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem finite_relative_common_row {α β : Type*} [DecidableEq β]
    (I : Finset α) (U : Finset β) (A : α → Finset β)
    (hI : I.Nonempty) (hU : U.Nonempty) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : ∀ i ∈ I, A i ⊆ U) (hsize : ∀ i ∈ I, ρ*(U.card:ℝ) ≤ ((A i).card:ℝ)) :
    ∃ i₀ ∈ I, ∃ J ⊆ I, (ρ^2/2)*(I.card:ℝ) ≤ (J.card:ℝ) ∧
      ∀ j ∈ J, (ρ^2/2)*(U.card:ℝ) ≤ ((A i₀ ∩ A j).card:ℝ) := by
  have hUp : 0 < (U.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hU)
  obtain ⟨i,hi,J,hJI,hJ,hcount⟩ := finite_family_common_row I U A hI hU (mul_pos hρ hUp) hsub hsize
  refine ⟨i,hi,J,hJI,?_,?_⟩
  · have he : (ρ*(U.card:ℝ))^2/(U.card:ℝ) = ρ^2*(U.card:ℝ) := by field_simp
    rw [he] at hJ
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < 2*(U.card:ℝ))).1
    convert hJ using 1 <;> ring
  · intro j hj
    have he : (ρ*(U.card:ℝ))^2/(2*(U.card:ℝ)) = (ρ^2/2)*(U.card:ℝ) := by field_simp
    simpa only [he] using hcount j hj

 theorem finite_delete_interval {I J : Finset ℝ} (hJI : J ⊆ I) (z r : ℝ) :
    (J.card:ℝ)-scalarBallMass I z r ≤ ((J.filter fun y => r < |y-z|).card:ℝ) := by
  classical
  have hc := Finset.card_filter_add_card_filter_not (s := J) (p := fun y => |y-z| ≤ r)
  have hsmall : ((J.filter fun y => |y-z| ≤ r).card:ℝ) ≤ scalarBallMass I z r :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hJI))
  have he : (J.filter fun y => ¬ |y-z| ≤ r) = J.filter fun y => r < |y-z| := by
    simp only [not_le]
  rw [he] at hc
  have hcR : ((J.filter fun y => |y-z| ≤ r).card:ℝ)+
      ((J.filter fun y => r < |y-z|).card:ℝ) = (J.card:ℝ) := by exact_mod_cast hc
  linarith

end Falconer

end OAI
