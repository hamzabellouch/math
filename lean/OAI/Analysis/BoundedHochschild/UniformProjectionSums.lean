import OAI.Analysis.BoundedHochschild.PositiveCompleteAdditivity

namespace OAI

/-!
# Uniform summation of orthogonal projections

The positive case of the gliding-block argument in Ringrose, Theorem 4.7:
uniform decay on orthogonal sequences implies uniform complete additivity.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

private lemma disjoint_finset_sequence {I : Type v} (B : Finset I → Prop)
    (hB : ∀ s : Finset I, ∃ t : Finset I, Disjoint s t ∧ B t) :
    ∃ b : ℕ → Finset I, (∀ m n, m ≠ n → Disjoint (b m) (b n)) ∧ ∀ n, B (b n) := by
  classical
  let next (s : Finset I) := (hB s).choose
  have hn (s) : Disjoint s (next s) ∧ B (next s) := (hB s).choose_spec
  let c : ℕ → Finset I := Nat.rec ∅ (fun _ s => s ∪ next s)
  have hc (n) : c (n + 1) = c n ∪ next (c n) := rfl
  have hm : Monotone c := monotone_nat_of_le_succ (fun n => by
    rw [hc]; exact Finset.subset_union_left)
  let b (n : ℕ) := next (c n)
  have hlt (m n : ℕ) (hmn : m < n) : Disjoint (b m) (b n) := by
    apply (hn (c n)).1.mono_left
    exact (show b m ⊆ c (m + 1) by rw [hc]; exact Finset.subset_union_right).trans
      (hm (Nat.succ_le_iff.mpr hmn))
  refine ⟨b, ?_, fun n => (hn (c n)).2⟩
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hlt m n h
  · exact (hlt n m h).symm

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma orthogonal_projection_finset_sum_le {I : Type v} (p : I → M)
    (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i ≠ j → p i * p j = 0)
    {P : M} (hP : IsStarProjection P) (hu : ∀ i, p i ≤ P) (s : Finset I) :
    (∑ i ∈ s, p i) ≤ P := by
  classical
  apply ((orthogonal_projection_finset_sum p hp ho s).le_iff_mul_eq_left hP).mpr
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => ((hp i).le_iff_mul_eq_left hP).mp (hu i))

omit [StarOrderedRing M] in
/-- Uniform orthogonal-sequence decay forces uniformly small remainders of
arbitrary orthogonal sums. Only the positive, completely additive case is used. -/
theorem uniform_orthogonal_sum_remainder
    (K : Set (StrongDual ℂ M))
    (hadd : ∀ F ∈ K, CompletelyAdditive F)
    (hdecay : ∀ q : ℕ → M, (∀ n, IsStarProjection (q n)) →
      (∀ m n, m ≠ n → q m * q n = 0) → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ F ∈ K, ‖F (q n)‖ < ε)
    (I : Type u) (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i ≠ j → p i * p j = 0)
    (P : M) (hP : IsStarProjection P) (hu : ∀ i, p i ≤ P)
    (hl : ∀ r : M, IsStarProjection r → (∀ i, p i ≤ r) → P ≤ r)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset I, ∀ F ∈ K, (F (P - ∑ i ∈ s, p i)).re < ε := by
  classical
  by_contra hfail
  push Not at hfail
  have hb : ∀ s : Finset I, ∃ t : Finset I, Disjoint s t ∧
      ∃ F ∈ K, ε / 2 < (F (∑ i ∈ t, p i)).re := by
    intro s
    obtain ⟨F, hFK, hbad⟩ := hfail s
    have ht := Complex.continuous_re.tendsto (F P) |>.comp (hadd F hFK I p hp ho P hP hu hl)
    have hevent : ∀ᶠ t : Finset I in atTop,
        (F P).re - ε / 2 < (∑ i ∈ t, F (p i)).re :=
      (tendsto_order.mp ht).1 _ (by linarith)
    obtain ⟨t, hts, htlarge⟩ := ((eventually_ge_atTop s).and hevent).exists
    refine ⟨t \ s, Finset.disjoint_sdiff, F, hFK, ?_⟩
    have hsum : (∑ i ∈ t \ s, p i) + ∑ i ∈ s, p i = ∑ i ∈ t, p i :=
      Finset.sum_sdiff hts
    have hval := congrArg (fun a : M => (F a).re) hsum
    simp only [map_add, Complex.add_re, map_sum] at hval
    simp only [map_sub, Complex.sub_re, map_sum] at hbad
    rw [map_sum]
    linarith
  obtain ⟨b, hdis, hb⟩ := disjoint_finset_sequence
    (fun t : Finset I => ∃ F ∈ K, ε / 2 < (F (∑ i ∈ t, p i)).re) hb
  let q (n : ℕ) : M := ∑ i ∈ b n, p i
  have hq (n) : IsStarProjection (q n) := orthogonal_projection_finset_sum p hp ho (b n)
  have hqo (m n : ℕ) (hmn : m ≠ n) : q m * q n = 0 := by
    dsimp [q]
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro j hj
    exact ho i j (fun hij => Finset.disjoint_left.mp (hdis m n hmn) hi (hij ▸ hj))
  obtain ⟨n, hn⟩ := (hdecay q hq hqo (ε / 2) (half_pos hε)).exists
  obtain ⟨F, hFK, hlarge⟩ := hb n
  have hsmall := hn F hFK
  have hre := Complex.re_le_norm (F (q n))
  exact (not_lt_of_ge (le_trans hlarge.le hre)) hsmall

end KadisonRingrose
end BoundedHochschild

end

end OAI
