import OAI.Analysis.BoundedHochschild.TraceFreeProjectionJoins
import OAI.Analysis.BoundedHochschild.PartialIsoProducts

namespace OAI

/-! Comparison bounds for joins, independent of any scalar trace. -/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma orthogonal_projection_sum_range (q : ℕ → M)
    (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (n : ℕ) :
    IsStarProjection (∑ i ∈ Finset.range n, q i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      apply ih.add (hq n)
      rw [Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro i hi
      exact horth i n (Nat.ne_of_lt (Finset.mem_range.mp hi))

/-- If two projections embed into orthogonal target projections, their join
embeds into the sum of those targets. -/
theorem projection_join_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p₁ p₂ q₁ q₂ : M} (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂)
    (hq₁ : IsStarProjection q₁) (hq₂ : IsStarProjection q₂) (hqorth : q₁ * q₂ = 0)
    (a b : PartialIso M) (hai : a.initial = p₁) (haf : a.final ≤ q₁)
    (hbi : b.initial = p₂) (hbf : b.final ≤ q₂) :
    ∃ t : PartialIso M, t.final ≤ q₁ + q₂ ∧ p₁ ≤ t.initial ∧ p₂ ≤ t.initial ∧
      ∀ r : M, IsStarProjection r → p₁ ≤ r → p₂ ≤ r → t.initial ≤ r := by
  obtain ⟨v, hvi, horth, hj, hpj, hqj, hleast⟩ :=
    exists_trace_free_projection_join e p₁ p₂ hp₁ hp₂
  have hcomp : (adjointPartialIso v).final ≤ b.initial := by simpa [hbi] using hvi
  let c := composePartialIso b (adjointPartialIso v) hcomp
  have hci : c.initial = v.final := by simp [c]
  have hcf : c.final ≤ q₂ := (composePartialIso_final_le b _ hcomp).trans hbf
  have haci : a.initial * c.initial = 0 := by rw [hai, hci]; exact horth
  have hacf : a.final * c.final = 0 :=
    projection_orthogonal_mono a.final_proj c.final_proj hq₁ hq₂ haf hcf hqorth
  let t := a.orthogonalSum c haci hacf
  have hti : t.initial = p₁ + v.final := by
    rw [show t.initial = a.initial + c.initial from PartialIso.orthogonalSum_initial _ _ _ _,
      hai, hci]
  refine ⟨t, ?_, by rw [hti]; exact hpj, by rw [hti]; exact hqj, ?_⟩
  · rw [show t.final = a.final + c.final from PartialIso.orthogonalSum_final _ _ _ _]
    exact add_le_add haf hcf
  · intro r hr hpr hqr
    rw [hti]
    exact hleast r hr hpr hqr

/-- Finite joins of projections equivalent to orthogonal projections embed
into the corresponding finite orthogonal sum. -/
theorem finite_join_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p q : ℕ → M) (hp : ∀ n, IsStarProjection (p n))
    (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q n)
    (n : ℕ) :
    ∃ v : PartialIso M, v.final ≤ ∑ i ∈ Finset.range n, q i ∧
      (∀ i < n, p i ≤ v.initial) ∧
      ∀ r : M, IsStarProjection r → (∀ i < n, p i ≤ r) → v.initial ≤ r := by
  classical
  induction n with
  | zero =>
      refine ⟨0, by simp, by simp, ?_⟩
      intro r hr _
      simpa using hr.nonneg
  | succ n ih =>
      obtain ⟨a, haf, hau, hal⟩ := ih
      obtain ⟨b, hbi, hbf⟩ := hembed n
      have hsum : IsStarProjection (∑ i ∈ Finset.range n, q i) := by
        exact orthogonal_projection_sum_range q hq horth n
      have hsumorth : (∑ i ∈ Finset.range n, q i) * q n = 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro i hi
        exact horth i n (Nat.ne_of_lt (Finset.mem_range.mp hi))
      obtain ⟨t, htf, hat, hpt, hleast⟩ := projection_join_subequivalence e
        a.initial_proj (hp n) hsum (hq n) hsumorth a b rfl haf hbi hbf
      refine ⟨t, ?_, ?_, ?_⟩
      · simpa only [Finset.sum_range_succ] using htf
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hin | rfl
        · exact (hau i hin).trans hat
        · exact hpt
      · intro r hr hpr
        exact hleast r hr (hal r hr (fun i hi => hpr i (Nat.lt_succ_of_lt hi)))
          (hpr n (Nat.lt_succ_self n))

end KadisonRingrose
end BoundedHochschild

end

end OAI
