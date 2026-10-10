import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

open Filter Topology

namespace UnitalTomsWinter

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A]

def CuntzSubequiv (a b : A) : Prop :=
  a ∈ closure (Set.range fun x : A => star x * b * x)

theorem cuntzSubequiv_iff_sequence {a b : A} :
    CuntzSubequiv a b ↔
      ∃ x : ℕ → A, Tendsto (fun n => star (x n) * b * x n) atTop (𝓝 a) := by
  constructor
  · intro h
    obtain ⟨y, hy, ht⟩ := mem_closure_iff_seq_limit.mp h
    choose x hx using hy
    exact ⟨x, by simpa only [hx] using ht⟩
  · rintro ⟨x, hx⟩
    exact mem_closure_of_tendsto hx (Filter.Eventually.of_forall fun n => ⟨x n, rfl⟩)

theorem cuntzSubequiv_iff_norm {a b : A} :
    CuntzSubequiv a b ↔
      ∀ ε : ℝ, 0 < ε → ∃ x : A, ‖star x * b * x - a‖ < ε := by
  simp only [CuntzSubequiv, Metric.mem_closure_iff, Set.exists_range_iff,
    dist_eq_norm, norm_sub_rev]

theorem cuntzSubequiv_of_exact {a b x : A} (h : star x * b * x = a) :
    CuntzSubequiv a b :=
  subset_closure ⟨x, h⟩

theorem zero_cuntzSubequiv (b : A) : CuntzSubequiv 0 b :=
  cuntzSubequiv_of_exact (x := 0) (by simp)

@[simp] theorem cuntzSubequiv_zero_iff (a : A) : CuntzSubequiv a 0 ↔ a = 0 := by
  simp [CuntzSubequiv, Set.range_const]

theorem CuntzSubequiv.of_tendsto {a b : A} {u : ℕ → A}
    (h : ∀ n, CuntzSubequiv (u n) b) (hu : Tendsto u atTop (𝓝 a)) :
    CuntzSubequiv a b :=
  isClosed_closure.mem_of_tendsto hu (Filter.Eventually.of_forall h)

theorem CuntzSubequiv.compress {b c : A} (h : CuntzSubequiv b c) (x : A) :
    CuntzSubequiv (star x * b * x) c := by
  obtain ⟨y, hy⟩ := cuntzSubequiv_iff_sequence.mp h
  apply cuntzSubequiv_iff_sequence.mpr
  refine ⟨fun n => y n * x, ?_⟩
  have ht := (hy.const_mul (star x)).mul_const x
  simpa only [star_mul, mul_assoc] using ht

theorem CuntzSubequiv.trans {a b c : A}
    (hab : CuntzSubequiv a b) (hbc : CuntzSubequiv b c) :
    CuntzSubequiv a c := by
  obtain ⟨x, hx⟩ := cuntzSubequiv_iff_sequence.mp hab
  exact CuntzSubequiv.of_tendsto (fun n => hbc.compress (x n)) hx

end UnitalTomsWinter

end

section

namespace UnitalTomsWinter
variable {B : Type*} [NonUnitalCStarAlgebra B]

lemma projection_norm_le_one {p : B} (hp : IsStarProjection p) : ‖p‖ ≤ 1 := by
  exact IsStarProjection.norm_le p hp

lemma projection_compression_norm_le {q : B} (hq : IsStarProjection q) (x : B) :
    ‖q * x * q‖ ≤ ‖x‖ := by
  calc
    ‖q * x * q‖ ≤ ‖q * x‖ * ‖q‖ := norm_mul_le _ _
    _ ≤ ‖q * x‖ := mul_le_of_le_one_right (norm_nonneg _) (projection_norm_le_one hq)
    _ ≤ ‖q‖ * ‖x‖ := norm_mul_le _ _
    _ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg _) (projection_norm_le_one hq)

theorem CuntzSubequiv.exists_corner_witness {a b p q : B}
    (h : CuntzSubequiv a b) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpb : p * b = b) (hbp : b * p = b) (hqa : q * a = a) (haq : a * q = a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : B, p * x = x ∧ x * q = x ∧ ‖star x * b * x - a‖ < ε := by
  obtain ⟨X, hX⟩ := cuntzSubequiv_iff_norm.mp h ε hε
  refine ⟨p * X * q, ?_, ?_, ?_⟩
  · simp only [← mul_assoc, hp.isIdempotentElem.eq]
  · simp only [mul_assoc, hq.isIdempotentElem.eq]
  · have heq : star (p * X * q) * b * (p * X * q) - a =
        q * (star X * b * X - a) * q := by
      have hbp' (y : B) : b * (p * y) = b * y := by rw [← mul_assoc, hbp]
      simp only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
        mul_sub, sub_mul]
      simp only [mul_assoc, hpb, hbp', hqa, haq]
    rw [heq]
    exact (projection_compression_norm_le hq _).trans_lt hX
end UnitalTomsWinter
end

end OAI
