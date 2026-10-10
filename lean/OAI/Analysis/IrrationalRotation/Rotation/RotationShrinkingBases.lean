import OAI.Analysis.IrrationalRotation.Model.Rotation
import OAI.Analysis.IrrationalRotation.Analysis.BackgroundBumps
import OAI.Analysis.IrrationalRotation.Sampling.SyndeticSampling

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace Invariant233.Rotation

theorem nsmul_injective_of_irrational {θ : ℝ} (hθ : Irrational θ) :
    Function.Injective (fun n : ℕ => n • (θ : Circle)) := by
  apply injective_nsmul_iff_not_isOfFinAddOrder.mpr
  rw [AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div]
  rintro ⟨q, hq⟩
  exact hθ.ne_rat q (by simpa using hq.symm)

theorem exists_shrinking_positive_minorant (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ (∀ n, r n ≤ a n) ∧
      (∀ n, r (n + 1) ≤ r n / 2) ∧
      (∀ n, r n ≤ 1 / ((n : ℝ) + 1)) ∧
      Antitone r ∧ Tendsto r atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun n => Nat.rec (min (a 0) 1)
    (fun k t => min (t / 2) (min (a (k + 1)) (1 / ((k : ℝ) + 2)))) n
  have hzero : r 0 = min (a 0) 1 := rfl
  have hsucc (n : ℕ) : r (n + 1) =
      min (r n / 2) (min (a (n + 1)) (1 / ((n : ℝ) + 2))) := rfl
  have hpos : ∀ n, 0 < r n := by
    intro n
    induction n with
    | zero => rw [hzero]; exact lt_min (ha 0) zero_lt_one
    | succ n ih => rw [hsucc]; exact lt_min (by positivity) (lt_min (ha _) (by positivity))
  have hbound : ∀ n, r n ≤ a n := by
    intro n
    cases n with
    | zero => rw [hzero]; exact min_le_left _ _
    | succ n => rw [hsucc]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hhalf (n : ℕ) : r (n + 1) ≤ r n / 2 := by
    rw [hsucc]
    exact min_le_left _ _
  have hcap : ∀ n, r n ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    cases n with
    | zero => simpa only [hzero, Nat.cast_zero, zero_add, div_one] using min_le_right (a 0) 1
    | succ n =>
      rw [hsucc]
      have h := (min_le_right (r n / 2) _).trans
        (min_le_right (a (n + 1)) (1 / ((n : ℝ) + 2)))
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  have hanti : Antitone r := antitone_nat_of_succ_le fun n =>
    (hhalf n).trans (by linarith [hpos n])
  refine ⟨r, hpos, hbound, hhalf, hcap, hanti, ?_⟩
  exact squeeze_zero (fun n => (hpos n).le) hcap
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem exists_shrinking_disjoint_radii {θ : ℝ} (hθ : Irrational θ) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧
      (∀ n, r (n + 1) ≤ r n / 2) ∧
      (∀ n, r n ≤ 1 / ((n : ℝ) + 1)) ∧
      Antitone r ∧ Tendsto r atTop (𝓝 0) ∧
      ∀ n, Pairwise (fun i j : Fin (n + 1) =>
        Disjoint
          ((fun x : Circle => x + (i : ℕ) • (θ : Circle)) '' Metric.closedBall 0 (r n))
          ((fun x : Circle => x + (j : ℕ) • (θ : Circle)) '' Metric.closedBall 0 (r n))) := by
  classical
  have hinj := nsmul_injective_of_irrational hθ
  have hsep (n : ℕ) := BackgroundCost.exists_disjoint_closedBalls
    (fun i : Fin (n + 1) => (i : ℕ) • (θ : Circle))
    (fun i j hij => Fin.ext (hinj hij))
  choose a ha hdisj using hsep
  obtain ⟨r, hr, hra, hhalf, hcap, hanti, hlim⟩ :=
    exists_shrinking_positive_minorant a ha
  refine ⟨r, hr, hhalf, hcap, hanti, hlim, ?_⟩
  intro n i j hij
  have hsub (k : Fin (n + 1)) :
      (fun x : Circle => x + (k : ℕ) • (θ : Circle)) '' Metric.closedBall 0 (r n) ⊆
        Metric.closedBall ((k : ℕ) • (θ : Circle)) (a n) := by
    rintro y ⟨x, hx, rfl⟩
    change dist (x + (k : ℕ) • (θ : Circle)) ((k : ℕ) • (θ : Circle)) ≤ a n
    simpa only [zero_add] using (show dist (x + (k : ℕ) • (θ : Circle))
      (0 + (k : ℕ) • (θ : Circle)) ≤ a n by
        rw [dist_add_right]
        exact hx.trans (hra n))
  exact (hdisj n hij).mono (hsub i) (hsub j)

theorem exists_uniform_two_sided_positive_hitting_window {θ : ℝ} (hθ : Irrational θ)
    (B : Set Circle) (hB : IsOpen B) (hne : B.Nonempty) :
    ∃ L : ℕ, ∀ x : Circle,
      (∃ k : ℕ, 0 < k ∧ k ≤ L ∧ x + k • (θ : Circle) ∈ B) ∧
      (∃ k : ℕ, 0 < k ∧ k ≤ L ∧ x - k • (θ : Circle) ∈ B) := by
  obtain ⟨Lplus, hplus⟩ := SyndeticSampling.exists_uniform_hitting_window hθ B hB hne
  obtain ⟨Lminus, hminus⟩ := SyndeticSampling.exists_uniform_hitting_window hθ.neg B hB hne
  refine ⟨max (Lplus + 1) (Lminus + 1), ?_⟩
  intro x
  constructor
  · obtain ⟨k, hk, hmem⟩ := hplus (x + (θ : Circle))
    refine ⟨k + 1, by omega, (Nat.add_le_add_right hk 1).trans (le_max_left _ _), ?_⟩
    simpa only [add_nsmul, one_nsmul, add_assoc, add_comm, add_left_comm] using hmem
  · obtain ⟨k, hk, hmem⟩ := hminus (x - (θ : Circle))
    refine ⟨k + 1, by omega, (Nat.add_le_add_right hk 1).trans (le_max_right _ _), ?_⟩
    simpa only [AddCircle.coe_neg, smul_neg, add_nsmul, one_nsmul, sub_eq_add_neg,
      neg_add, add_assoc, add_comm, add_left_comm] using hmem

theorem no_short_return_of_disjoint_translates {θ : ℝ} {B : Set Circle} {n : ℕ}
    (hd : Pairwise (fun i j : Fin (n + 1) =>
      Disjoint ((fun x : Circle => x + (i : ℕ) • (θ : Circle)) '' B)
        ((fun x : Circle => x + (j : ℕ) • (θ : Circle)) '' B)))
    {x : Circle} (hx : x ∈ B) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    x + k • (θ : Circle) ∉ B := by
  intro hreturn
  let i : Fin (n + 1) := ⟨0, by omega⟩
  let j : Fin (n + 1) := ⟨k, by omega⟩
  have hij : i ≠ j := by
    intro h
    have he := congrArg Fin.val h
    change 0 = k at he
    omega
  have hleft : x + k • (θ : Circle) ∈
      (fun y : Circle => y + (i : ℕ) • (θ : Circle)) '' B :=
    ⟨x + k • (θ : Circle), hreturn, by simp [i]⟩
  have hright : x + k • (θ : Circle) ∈
      (fun y : Circle => y + (j : ℕ) • (θ : Circle)) '' B := ⟨x, hx, rfl⟩
  exact Set.disjoint_left.mp (hd hij) hleft hright

theorem exists_nested_open_bases {θ : ℝ} (hθ : Irrational θ) :
    ∃ B : ℕ → Set Circle,
      (∀ n, IsOpen (B n) ∧ (0 : Circle) ∈ B n) ∧
      Antitone B ∧
      (∀ n, closure (B (n + 1)) ⊆ B n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
        ∀ x ∈ B n, ∀ y ∈ B n, dist x y < ε) ∧
      (∀ n, Pairwise (fun i j : Fin (n + 1) =>
        Disjoint ((fun x : Circle => x + (i : ℕ) • (θ : Circle)) '' B n)
          ((fun x : Circle => x + (j : ℕ) • (θ : Circle)) '' B n))) ∧
      (∀ n x, x ∈ B n → ∀ k : ℕ, 0 < k → k ≤ n →
        x + k • (θ : Circle) ∉ B n ∧ x - k • (θ : Circle) ∉ B n) ∧
      (∀ n, ∃ L : ℕ, ∀ x : Circle,
        (∃ k : ℕ, 0 < k ∧ k ≤ L ∧ x + k • (θ : Circle) ∈ B n) ∧
        (∃ k : ℕ, 0 < k ∧ k ≤ L ∧ x - k • (θ : Circle) ∈ B n)) := by
  obtain ⟨r, hr, hhalf, _hcap, hanti, hlim, hsep⟩ := exists_shrinking_disjoint_radii hθ
  let B : ℕ → Set Circle := fun n => Metric.ball 0 (r n)
  have hB (n : ℕ) : IsOpen (B n) ∧ (0 : Circle) ∈ B n :=
    ⟨Metric.isOpen_ball, Metric.mem_ball_self (hr n)⟩
  have hdisj (n : ℕ) : Pairwise (fun i j : Fin (n + 1) =>
      Disjoint ((fun x : Circle => x + (i : ℕ) • (θ : Circle)) '' B n)
        ((fun x : Circle => x + (j : ℕ) • (θ : Circle)) '' B n)) := by
    intro i j hij
    exact (hsep n hij).mono (Set.image_mono Metric.ball_subset_closedBall)
      (Set.image_mono Metric.ball_subset_closedBall)
  refine ⟨B, hB, ?_, ?_, ?_, hdisj, ?_, ?_⟩
  · intro m n hmn
    exact Metric.ball_subset_ball (hanti hmn)
  · intro n
    exact (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball ((hhalf n).trans_lt (by linarith [hr n])))
  · intro ε hε
    have hevent : ∀ᶠ n in atTop, r n < ε / 2 :=
      hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    refine ⟨N, ?_⟩
    intro n hn x hx y hy
    have hx' : dist x 0 < r n := hx
    have hy' : dist 0 y < r n := by
      change dist y 0 < r n at hy
      simpa only [dist_comm] using hy
    have ht := dist_triangle x (0 : Circle) y
    have hn' := hN n hn
    linarith
  · intro n x hx k hk hkn
    refine ⟨no_short_return_of_disjoint_translates (hdisj n) hx hk hkn, ?_⟩
    intro hback
    have h := no_short_return_of_disjoint_translates (hdisj n) hback hk hkn
    exact h (by simpa only [sub_add_cancel] using hx)
  · intro n
    exact exists_uniform_two_sided_positive_hitting_window hθ (B n) (hB n).1 ⟨0, (hB n).2⟩

end Invariant233.Rotation

end

end OAI
