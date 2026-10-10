import OAI.MeasureTheory.Falconer.Angular.ProjectionAngularGeometry
import OAI.MeasureTheory.Falconer.Estimates.ParallelExceptional

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem regularized_projection_card (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) {m : ℝ → ℝ} {N B : ℕ} {δ lam : ℝ}
    (hr : RegularizedProfileData Q ρ N B δ lam m)
    {p u : ℕ} (hpu : p ≤ u) (huN : u ≤ N) {P : CellPath} (hP : P.length = p) :
    ((projectionTestCells Q ρ p u P).card:ℝ) ≤
      64*((2:ℝ)^N)^(m u-m p+6*lam) := by
  have hc : ((projectionTestCells Q ρ p u P).card:ℝ) ≤
      ((occupiedCenterCells Q ρ u (Q.descendant P).center (3/(2:ℝ)^p)).card:ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (projection_cells_subset_ball Q hQ ρ p u hP))
  have hp := hr.packing p u hpu huN (Q.descendant P).center 3 (by norm_num)
  norm_num [hQ] at hp
  exact hc.trans hp

theorem regularized_projection_strip_sum (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) {m : ℝ → ℝ} {N B : ℕ} {δ lam sig : ℝ}
    (hr : RegularizedProfileData Q ρ N B δ lam m) (hN : 0 < N)
    (hlam : 0 < lam) (hsig : 0 < sig)
    {p u : ℕ} (hpu : p ≤ u) (huN : u ≤ N) {P : CellPath} (hP : P.length = p) :
    ∑ cc ∈ (projectionTestCells Q ρ p u P).product (projectionTestCells Q ρ p u P),
      stripHitBound (2/(2:ℝ)^u*((2:ℝ)^N)^(1000*sig))
        ((Q.descendant cc.1).center-(Q.descendant cc.2).center) ≤
      ENNReal.ofReal ((247936*Real.pi)*(1+2*(N:ℝ))*((2:ℝ)^N)^
        (m u-m p+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+1000*sig+12*lam)) := by
  apply (projection_strip_sum_rows Q hQ ρ p u hP _).trans
  let Z := (3874*Real.pi)*(1+2*(N:ℝ))*((2:ℝ)^N)^
    (height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+1000*sig+6*lam)
  have hz : 0 ≤ Z := by dsimp [Z]; positivity
  have hh : (∑ a ∈ projectionTestCells Q ρ p u P,
      ∑ c ∈ parallelTestCells Q ρ p u a,
        stripHitBound (2/(2:ℝ)^u*((2:ℝ)^N)^(1000*sig))
          (quarterTurn ((Q.descendant c).center-(Q.descendant a).center))) ≤
      ∑ _a ∈ projectionTestCells Q ρ p u P, ENNReal.ofReal Z := by
    apply Finset.sum_le_sum
    intro a ha
    exact regularized_parallel_strip_sum Q hQ ρ hr hN hlam hsig hpu huN
      ((mem_dyadicPaths u a).mp (Finset.mem_filter.mp ha).1)
  apply hh.trans
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hc := mul_le_mul_of_nonneg_right (regularized_projection_card Q hQ ρ hr hpu huN hP) hz
  apply hc.trans_eq
  dsimp [Z]
  have hRp : 0 < (2:ℝ)^N := by positivity
  calc
    _ = (247936*Real.pi)*(1+2*(N:ℝ))*
      (((2:ℝ)^N)^(m u-m p+6*lam)*((2:ℝ)^N)^
        (height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+1000*sig+6*lam)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hRp]
      congr 2
      ring

theorem uniform_projection_exceptional {lam sig : ℝ} (hlam : 0 < lam) (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 →
      ∀ (ρ : Measure Plane) (m : ℝ → ℝ) (B : ℕ) (δ : ℝ),
      RegularizedProfileData Q ρ N B δ lam m →
      ∀ p u : ℕ, p ≤ u → u ≤ N → ∀ P : CellPath, P.length = p →
      sourceArcLength (projectionGoodSet Q ρ p u P
        (2/(2:ℝ)^u*((2:ℝ)^N)^(1000*sig))
        (((2:ℝ)^N)^(m u-m p+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+2000*(lam+sig))))ᶜ ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  obtain ⟨N₁,hN₁⟩ := fixed_linear_subpower (247936*Real.pi) (by positivity) (add_pos hlam hsig)
  refine ⟨max 1 N₁,?_⟩
  intro N hN Q hQ ρ m B δ hr p u hpu huN P hP
  have hb := regularized_projection_strip_sum Q hQ ρ hr (by omega) hlam hsig hpu huN hP
  apply (projectionGoodSet_compl_bound Q ρ p u P (by positivity) (by positivity)).trans
  apply (ENNReal.div_le_div_right hb _).trans
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact angular_ratio_absorption hlam hsig (hN₁ N ((le_max_right _ _).trans hN))

end PlanarFalconer

end OAI
