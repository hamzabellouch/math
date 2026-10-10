import OAI.MeasureTheory.Falconer.Geometry.FinitePrefixBallBound

namespace OAI

/-! Interpolate finite prefix tests between selected block depths. Only the
actual maximum depth gap is charged, before passing to geometric balls. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem pointPrefixFiber_subset_take (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    {a n : ℕ} (ha : a ≤ n) (p : CellPath 2) :
    pointPrefixFiber P l n p ⊆ pointPrefixFiber P l a (p.take a) := by
  intro x hx
  obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hx,?_⟩
  have hh := congrArg (List.take a) he
  simpa only [List.take_take,Nat.min_eq_left ha] using hh

theorem dyadic_prefix_gap_bound {a n B : ℕ} (ha : a ≤ n) (hgap : n ≤ a+B) {s : ℝ} (hs : 0 ≤ s) :
    (1/(2:ℝ)^a)^s ≤ ((2:ℝ)^B)^s*(1/(2:ℝ)^n)^s := by
  have hp : (2:ℝ)^n = (2:ℝ)^a*(2:ℝ)^(n-a) := by rw [← pow_add,Nat.add_sub_of_le ha]
  have hbase : 1/(2:ℝ)^a ≤ (2:ℝ)^B*(1/(2:ℝ)^n) := by
    rw [hp]
    rw [mul_one_div]
    have hh : (2:ℝ)^(n-a) ≤ (2:ℝ)^B := pow_le_pow_right₀ (by norm_num) (by omega)
    apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^a*(2:ℝ)^(n-a))).2
    calc
      _ = (2:ℝ)^(n-a) := by field_simp
      _ ≤ _ := hh
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1/(2:ℝ)^a) hbase hs
  rwa [Real.mul_rpow (by positivity : 0 ≤ (2:ℝ)^B) (by positivity : 0 ≤ 1/(2:ℝ)^n)] at hh

theorem finite_block_prefix_ball_bound {N B : ℕ} {s K : ℝ} (hs : 0 ≤ s) (hK : 1 ≤ K)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (htests : ∀ n ≤ N, ∃ a ≤ n, n ≤ a+B ∧
      ∀ p ∈ (P.image l).image (List.take a),
        ((pointPrefixFiber P l a p).card:ℝ) ≤ K*(1/(2:ℝ)^a)^s*(P.card:ℝ)) :
    NormalizedFiniteBallBound (1/(2:ℝ)^N) s (49*(K*((2:ℝ)^B)^s)*4^s) P := by
  have hKB : 1 ≤ K*((2:ℝ)^B)^s := by
    have hh : 1 ≤ ((2:ℝ)^B)^s :=
      Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hs
    simpa using mul_le_mul hK hh (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
  apply finite_prefix_ball_bound hs hKB Q hQ P l hleaf
  intro n hn p hp
  obtain ⟨a,ha,hgap,hbound⟩ := htests n hn
  have hpa : p.take a ∈ (P.image l).image (List.take a) := by
    obtain ⟨v,hv,hvp⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨v,hv,?_⟩
    have hh := congrArg (List.take a) hvp
    simpa only [List.take_take,Nat.min_eq_left ha] using hh
  calc
    _ ≤ ((pointPrefixFiber P l a (p.take a)).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (pointPrefixFiber_subset_take P l ha p))
    _ ≤ K*(1/(2:ℝ)^a)^s*(P.card:ℝ) := hbound _ hpa
    _ ≤ K*(((2:ℝ)^B)^s*(1/(2:ℝ)^n)^s)*(P.card:ℝ) := by
      gcongr
      exact dyadic_prefix_gap_bound ha hgap hs
    _ = _ := by ring

end Falconer

end OAI
