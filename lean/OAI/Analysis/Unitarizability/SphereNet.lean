import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith

namespace OAI

/-! Quarter-nets and their cardinality bounds. Volume comparison with
radii 1/8 and 9/8 gives the constant 9^m. -/
noncomputable section
namespace Dixmier
namespace SphereNet
open Set Metric MeasureTheory Module
open scoped ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Function in
 theorem quarter_separated_card (s : Finset E) (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (h : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → (1/4 : ℝ) ≤ ‖c-d‖) : s.card ≤ 9 ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := 1/8
  let ρ : ℝ := 9/8
  have ρpos : 0 < ρ := by norm_num [ρ]
  set A := ⋃ c ∈ s, ball (c : E) δ with hA
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) δ) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert h c hc d hd hcd using 1
    norm_num [δ]
  have A_subset : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + 1 := by rw [dist_zero_right]; exact add_le_add le_rfl (hs x hx)
      _ = ρ := by norm_num [δ, ρ]
  have I : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [hA, measure_biUnion_finset D (fun c _ => measurableSet_ball)]
        have hd : 0 < δ := by norm_num [δ]
        simp only [μ.addHaar_ball_of_pos _ hd, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono A_subset
      _ = _ := by simp only [μ.addHaar_ball_of_pos _ ρpos]
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤ ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) ≤ (9 : ℝ) ^ finrank ℝ E := by
    have hh := ENNReal.toReal_le_of_le_ofReal (pow_nonneg ρpos.le _) J
    simpa [ρ, δ, div_eq_mul_inv, mul_pow] using hh
  exact_mod_cast K

/-- A quarter-net with all centers on the unit sphere and
at most 9^dim centers. -/
theorem exists_quarter_net : ∃ s : Finset E,
    (∀ x ∈ s, ‖x‖ = 1) ∧ s.card ≤ 9 ^ finrank ℝ E ∧
      ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x-y‖ ≤ (1/4 : ℝ) := by
  classical
  let C : Set ℕ := {n | ∃ s : Finset E, s.card = n ∧ (∀ x ∈ s, ‖x‖ = 1) ∧
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1/4 : ℝ) ≤ ‖x-y‖}
  have hnonempty : C.Nonempty := ⟨0, ∅, by simp⟩
  have hbounded : BddAbove C := by
    refine ⟨9 ^ finrank ℝ E, ?_⟩
    rintro n ⟨s, rfl, hs, hsep⟩
    exact quarter_separated_card s (fun x hx => (hs x hx).le) hsep
  obtain ⟨s, hcard, hs, hsep⟩ := Nat.sSup_mem hnonempty hbounded
  refine ⟨s, hs, quarter_separated_card s (fun x hx => (hs x hx).le) hsep, ?_⟩
  intro x hx
  by_contra hnot
  push Not at hnot
  have hxnot : x ∉ s := by
    intro hmem
    have hh := hnot x hmem
    simp at hh
    linarith
  have hiunit : ∀ y ∈ insert x s, ‖y‖ = 1 := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hx
    · exact hs y hy
  have hisep : ∀ y ∈ insert x s, ∀ z ∈ insert x s, y ≠ z → (1/4 : ℝ) ≤ ‖y-z‖ := by
    intro y hy z hz hyz
    by_cases hyx : y = x
    · subst y
      have hz' : z ∈ s := (Finset.mem_insert.mp hz).resolve_left (Ne.symm hyz)
      exact (hnot z hz').le
    · have hy' : y ∈ s := (Finset.mem_insert.mp hy).resolve_left hyx
      by_cases hzx : z = x
      · subst z
        simpa only [norm_sub_rev] using (hnot y hy').le
      · have hz' : z ∈ s := (Finset.mem_insert.mp hz).resolve_left hzx
        exact hsep y hy' z hz' hyz
  have hbig : (insert x s).card ≤ sSup C := le_csSup hbounded ⟨insert x s, rfl, hiunit, hisep⟩
  rw [Finset.card_insert_of_notMem hxnot, hcard] at hbig
  omega

end SphereNet
end Dixmier

end

end OAI
