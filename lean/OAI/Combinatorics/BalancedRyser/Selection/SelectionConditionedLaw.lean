import OAI.Combinatorics.BalancedRyser.Selection.SelectionLaw
import OAI.Combinatorics.BalancedRyser.Selection.SelectionPushforward2

namespace OAI

namespace Balanced.Selection

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]
variable {G : Input I V} (law : OutputLaw G)

def OutputLaw.conditionOnSuccess (h : 0 < successMass law) : PMF (I → V) :=
  PMF.ofFintype (fun a => ENNReal.ofReal (law.weight a / successMass law)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun a _ => div_nonneg (law.nonnegative a) h.le)]
    rw [← Finset.sum_div]
    change ENNReal.ofReal (successMass law / successMass law) = 1
    rw [div_self (ne_of_gt h)]
    simp)

@[simp] theorem conditionOnSuccess_apply (h : 0 < successMass law) (a : I → V) :
    law.conditionOnSuccess h a = ENNReal.ofReal (law.weight a / successMass law) := rfl

@[simp] theorem conditionOnSuccess_real (h : 0 < successMass law) (a : I → V) :
    (law.conditionOnSuccess h a).toReal = law.weight a / successMass law :=
  ENNReal.toReal_ofReal (div_nonneg (law.nonnegative a) h.le)

theorem conditionOnSuccess_supported (h : 0 < successMass law) (a : I → V)
    (ha : 0 < law.conditionOnSuccess h a) : IsIndependentTransversal G a := by
  apply law.supported a
  have hratio : 0 < law.weight a / successMass law := ENNReal.ofReal_pos.mp ha
  exact (div_pos_iff.mp hratio).elim (fun z => z.1) (fun z => False.elim (not_lt_of_ge h.le z.2))

theorem conditioned_finset_probability (h : 0 < successMass law)
    (E : Finset (I → V)) :
    ((law.conditionOnSuccess h).toOuterMeasure (E : Set (I → V))).toReal =
      (∑ a ∈ E, law.weight a) / successMass law := by
  rw [PMF.toOuterMeasure_apply_finset]
  rw [ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top _ _)]
  simp only [conditionOnSuccess_real]
  rw [Finset.sum_div]

theorem conditioned_cylinder_probability (h : 0 < successMass law)
    (J : Finset I) (prescribed : I → V) :
    ((law.conditionOnSuccess h).toOuterMeasure
      (Finset.univ.filter (fun a : I → V => ∀ i ∈ J, a i = prescribed i) :
        Set (I → V))).toReal = cylinderMass law J prescribed / successMass law := by
  exact conditioned_finset_probability law h _

theorem conditioned_occupancy_probability (h : 0 < successMass law)
    {q : ℕ} {P D L : Type*} [Fintype P] [Fintype D] [Fintype L]
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P) (ρ : ℝ) :
    ((law.conditionOnSuccess h).toOuterMeasure
      (Finset.univ.filter (fun a : I → V =>
        ∃ ℓ : L, ((finalTracked A line T a ℓ).card : ℝ) < ρ * q) :
        Set (I → V))).toReal = occupancyFailureMass law A line T ρ / successMass law := by
  exact conditioned_finset_probability law h _

theorem conditioned_finset_probability_le (h : 0 < successMass law)
    (E : Finset (I → V)) {a₀ b : ℝ} (ha₀ : 0 < a₀)
    (hlower : a₀ ≤ successMass law) (hbound : (∑ a ∈ E, law.weight a) ≤ b) :
    ((law.conditionOnSuccess h).toOuterMeasure (E : Set (I → V))).toReal ≤ b / a₀ := by
  have hb : 0 ≤ b := (Finset.sum_nonneg (fun a _ => law.nonnegative a)).trans hbound
  calc
    _ = (∑ a ∈ E, law.weight a) / successMass law :=
      conditioned_finset_probability law h E
    _ ≤ b / successMass law := div_le_div_of_nonneg_right hbound h.le
    _ ≤ b / a₀ := div_le_div_of_nonneg_left hb ha₀ hlower

theorem conditioned_cylinder_probability_le (h : 0 < successMass law)
    (J : Finset I) (prescribed : I → V) {a₀ b : ℝ} (ha₀ : 0 < a₀)
    (hlower : a₀ ≤ successMass law) (hbound : cylinderMass law J prescribed ≤ b) :
    ((law.conditionOnSuccess h).toOuterMeasure
      (Finset.univ.filter (fun a : I → V => ∀ i ∈ J, a i = prescribed i) :
        Set (I → V))).toReal ≤ b / a₀ := by
  exact conditioned_finset_probability_le law h _ ha₀ hlower hbound

theorem conditioned_occupancy_probability_le (h : 0 < successMass law)
    {q : ℕ} {P D L : Type*} [Fintype P] [Fintype D] [Fintype L]
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P) (ρ : ℝ)
    {a₀ ε : ℝ} (ha₀ : 0 < a₀) (hlower : a₀ ≤ successMass law)
    (hbound : occupancyFailureMass law A line T ρ ≤ ε) :
    ((law.conditionOnSuccess h).toOuterMeasure
      (Finset.univ.filter (fun a : I → V =>
        ∃ ℓ : L, ((finalTracked A line T a ℓ).card : ℝ) < ρ * q) :
        Set (I → V))).toReal ≤ ε / a₀ := by
  exact conditioned_finset_probability_le law h _ ha₀ hlower hbound

theorem original_weight_eq_success_mul_conditioned (h : 0 < successMass law)
    (a : I → V) :
    law.weight a = successMass law * (law.conditionOnSuccess h a).toReal := by
  rw [conditionOnSuccess_real]
  exact (mul_div_cancel₀ (law.weight a) (ne_of_gt h)).symm.trans (by ring)

theorem conditioned_map_real (h : 0 < successMass law)
    {B : Type*} [DecidableEq B] (f : (I → V) → B) (b : B) :
    (((law.conditionOnSuccess h).map f) b).toReal =
      FinitePushforward.pushWeight f law.weight b / successMass law := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun a _ => by
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top)]
  simp only [FinitePushforward.pushWeight, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases he : f a = b
  · simp [he, div_nonneg (law.nonnegative a) h.le]
  · simp [he, Ne.symm he]

end
end Balanced.Selection

end OAI
