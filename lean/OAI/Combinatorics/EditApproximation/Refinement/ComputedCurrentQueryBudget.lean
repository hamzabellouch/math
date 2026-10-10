import OAI.Combinatorics.EditApproximation.Geometry.CurrentQueryInputs
import OAI.Combinatorics.EditApproximation.Refinement.ComputedGroupNumerical

namespace OAI

/-! Explicit polynomial same-index call budget after substituting the
computed window, cell, scale-label, sampling and rounding parameters. -/

namespace EditApproximation

def localCurrentBudget (window cells labels M Q inverseTheta : ℕ) : ℕ :=
  window * cells * labels * (624 * M * Q * inverseTheta ^ 2) + window * cells * M + window * M

theorem localCurrentBudget_poly (ell M window cells labels : ℕ) (hell : 4 ≤ ell)
    (hwindow : window ≤ 2 * ell ^ 2) (hcells : cells ≤ 1296 * ell ^ 82)
    (hlabels : labels ≤ 2 * ell) :
    localCurrentBudget window cells labels M (ell ^ 80) (ell ^ 40) ≤ M * ell ^ 256 := by
  have hfirst := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul hwindow hcells) hlabels)
    (le_rfl (a := 624 * M * ell ^ 80 * (ell ^ 40) ^ 2))
  have hsecond := Nat.mul_le_mul_right M (Nat.mul_le_mul hwindow hcells)
  have hthird := Nat.mul_le_mul_right M hwindow
  have h84 : ell ^ 84 ≤ ell ^ 245 := pow_le_pow_right₀ (by omega : 1 ≤ ell) (by decide : 84 ≤ 245)
  have h2 : ell ^ 2 ≤ ell ^ 245 := pow_le_pow_right₀ (by omega : 1 ≤ ell) (by decide : 2 ≤ 245)
  have hsecond' : 2 * ell ^ 2 * (1296 * ell ^ 82) * M ≤ 2592 * M * ell ^ 245 := by
    calc
      _ = 2592 * M * ell ^ 84 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h84
  have hthird' : 2 * ell ^ 2 * M ≤ 2 * M * ell ^ 245 := by
    calc
      _ = 2 * M * ell ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  have hsum : localCurrentBudget window cells labels M (ell ^ 80) (ell ^ 40) ≤
      3237410 * M * ell ^ 245 := by
    apply (Nat.add_le_add (Nat.add_le_add hfirst (hsecond.trans hsecond'))
      (hthird.trans hthird')).trans_eq
    ring
  have hconstant : 3237410 ≤ ell ^ 11 := by
    apply (show 3237410 ≤ (4 : ℕ) ^ 11 by norm_num).trans
    exact Nat.pow_le_pow_left hell 11
  calc
    _ ≤ 3237410 * M * ell ^ 245 := hsum
    _ ≤ ell ^ 11 * M * ell ^ 245 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right M hconstant)
    _ = M * ell ^ 256 := by ring

theorem computed_window_exponent_bound (N : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N) :
    computedSeedInitialExponent N + 8 ≤ 2 * inputSmallLog N ^ 2 := by
  have hh := (inputSmallLog_bounds N hN).1
  have hp : coarseExponent (inputSmallLog N) ≤ inputSmallLog N :=
    (Nat.sqrt_le_self _).trans ((Nat.sqrt_le_self _).trans (Nat.log_le_self _ _))
  have hmul := Nat.mul_le_mul (Nat.add_le_add_right hp 4) hh
  unfold computedSeedInitialExponent
  have hslack : 4 * inputSmallLog N + 8 ≤ inputSmallLog N ^ 2 := by nlinarith
  nlinarith only [hmul, hslack]

theorem computed_local_cell_budget (N : ℕ) (hell : 1 ≤ inputSmallLog N) :
    ((32 * inputSmallLog N + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2 ≤
      1296 * inputSmallLog N ^ 82 := by
  have hpower : 2 ^ (40 * smallLogExponent N) = inputSmallLog N ^ 40 := by
    unfold inputSmallLog
    rw [← pow_mul, Nat.mul_comm]
  rw [hpower]
  have hinner : (32 * inputSmallLog N + 2) * inputSmallLog N ^ 40 + 2 ≤
      36 * inputSmallLog N ^ 41 := by
    have ha := Nat.mul_le_mul_right (inputSmallLog N ^ 40) (show 32 * inputSmallLog N + 2 ≤
      34 * inputSmallLog N by omega)
    have hb : 2 ≤ 2 * inputSmallLog N ^ 41 := Nat.mul_le_mul_left 2 (one_le_pow₀ hell)
    calc
      _ ≤ 34 * inputSmallLog N * inputSmallLog N ^ 40 + 2 := Nat.add_le_add_right ha _
      _ ≤ 34 * inputSmallLog N * inputSmallLog N ^ 40 + 2 * inputSmallLog N ^ 41 :=
        Nat.add_le_add_left hb _
      _ = _ := by ring
  calc
    _ ≤ (36 * inputSmallLog N ^ 41) ^ 2 := Nat.pow_le_pow_left hinner 2
    _ = _ := by ring

theorem computed_refinement_window (N : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N)
    (A w : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ)) :
    (dyadicQueryWindow N w (refinementFactor A (inputSmallLog N)) (inputSmallLog N)).length ≤
      computedSeedInitialExponent N + 8 := by
  have hh := inputSmallLog_bounds N hN
  have hf : smallLogExponent N ≤ inputSmallLog N := (smallLogExponent N).lt_two_pow_self.le
  have he0 : smallLogExponent N ≤ computedSeedInitialExponent N := by
    have hfour := Nat.mul_le_mul_right (heightExponent N)
      (show 4 ≤ coarseExponent (inputSmallLog N) + 4 by omega)
    unfold computedSeedInitialExponent
    nlinarith only [hh.2, hf, hfour]
  apply refinement_query_window_length N (inputSmallLog N) (computedSeedInitialExponent N) A w (by omega)
  · simpa only [inputSmallLog, Nat.cast_pow, Nat.cast_ofNat] using
      pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) he0
  · exact hA.trans_eq (computedSeed_initial_factor N).symm

/-- The actual finite local shared/selected/online input cover is bounded
by M*ell^256 on every seed. The online-loop length premise is the literal
one-action-per-applicable-scale property proved for the physical program. -/
theorem computed_currentQueryInputCover_card {α : Type*} (source target : List α)
    (N P : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (parent : TargetInterval source.length) (A tau : ℚ)
    (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin (integerParameters N).M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws (integerParameters N).M (inputSmallLog N) (inputSmallLog N ^ 80))
    (q : TargetInterval target.length) (hw : 0 ≤ parentInitial q)
    (online : List (PhysicalRationalAction (integerParameters N).M target.length))
    (honline : online.length ≤
      (dyadicQueryWindow N (parentInitial q) (refinementFactor A (inputSmallLog N)) (inputSmallLog N)).length) :
    (currentQueryInputCover source target parent N P (inputSmallLog N) (40 * smallLogExponent N)
      (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N)) parentInitial
      child initial current draw q online).card ≤ (integerParameters N).M * inputSmallLog N ^ 256 := by
  let ell := inputSmallLog N
  let M := (integerParameters N).M
  let W := computedSeedInitialExponent N + 8
  let C := ((32 * ell + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2
  have hell8 : 8 ≤ ell := by omega
  have hM : 0 < M := by have h := (computed_branching_bounds N hN hell).1; omega
  have hlabels (b : ℕ) (hb : b ∈ dyadicScales N) : (groupDyadicScales M b ell).length ≤ 2 * ell := by
    obtain ⟨eb, _, rfl⟩ := List.mem_map.mp hb
    exact computed_group_scale_count N eb hN hell8
  have hwindow := computed_refinement_window N hN hell8 A (parentInitial q) hA
  have hkeys : (localGroupQueryKeys N ell (40 * smallLogExponent N)
      (refinementFactor A ell) parentInitial q).length ≤ W * C :=
    (localGroupQueryKeys_length N ell (40 * smallLogExponent N) (refinementFactor A ell)
      parentInitial q (by omega) hw).trans (Nat.mul_le_mul_right C hwindow)
  have hgroups := localCellGroupActions_length_refinement source target parent N P ell
    (40 * smallLogExponent N) (ell ^ 80) (computedSeedInitialExponent N) tau A
    parentInitial child initial current draw q (by omega) hw
  have hraw := currentQueryInputCover_card source target parent N P ell (40 * smallLogExponent N)
    (ell ^ 80) (2 * ell) tau (refinementFactor A ell) parentInitial child initial current draw q online
    hM (by omega) (one_le_pow₀ (by omega)) hlabels
  have hrawN : (currentQueryInputCover source target parent N P ell (40 * smallLogExponent N)
      (ell ^ 80) tau (refinementFactor A ell) parentInitial child initial current draw q online).card ≤
      (localGroupQueryKeys N ell (40 * smallLogExponent N) (refinementFactor A ell) parentInitial q).length *
        (2 * ell) * (624 * M * ell ^ 80 * (2 ^ (40 * smallLogExponent N)) ^ 2) +
      (localCellGroupActions source target parent N P ell (40 * smallLogExponent N) (ell ^ 80) tau
        (refinementFactor A ell) parentInitial child initial current draw q).length * M + online.length * M := by
    exact_mod_cast hraw
  have hFpower : (ell : ℚ) ≤ (2 : ℚ) ^ computedSeedInitialExponent N := by
    have hh := inputSmallLog_bounds N hN
    have hf : smallLogExponent N ≤ ell := (smallLogExponent N).lt_two_pow_self.le
    have hfour := Nat.mul_le_mul_right (heightExponent N)
      (show 4 ≤ coarseExponent ell + 4 by omega)
    have he : smallLogExponent N ≤ computedSeedInitialExponent N := by
      unfold computedSeedInitialExponent
      nlinarith only [hh.2, hf, hfour]
    simpa only [ell, inputSmallLog, Nat.cast_pow, Nat.cast_ofNat] using
      pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) he
  have hAbound : A ≤ (2 : ℚ) ^ computedSeedInitialExponent N := hA.trans_eq (computedSeed_initial_factor N).symm
  have hg : (localCellGroupActions source target parent N P ell (40 * smallLogExponent N) (ell ^ 80) tau
      (refinementFactor A ell) parentInitial child initial current draw q).length ≤ W * C :=
    hgroups hFpower hAbound
  have hbudget : (currentQueryInputCover source target parent N P ell (40 * smallLogExponent N)
      (ell ^ 80) tau (refinementFactor A ell) parentInitial child initial current draw q online).card ≤
      localCurrentBudget W C (2 * ell) M (ell ^ 80) (2 ^ (40 * smallLogExponent N)) := by
    exact hrawN.trans (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right (2 * ell) hkeys))
      (Nat.mul_le_mul_right M hg)) (Nat.mul_le_mul_right M (honline.trans hwindow)))
  have hpower : 2 ^ (40 * smallLogExponent N) = ell ^ 40 := by
    dsimp only [ell]
    unfold inputSmallLog
    rw [← pow_mul, Nat.mul_comm]
  rw [hpower] at hbudget
  exact hbudget.trans (localCurrentBudget_poly ell M W C (2 * ell)
    ((by decide : 4 ≤ (8 : ℕ)).trans hell8)
    (computed_window_exponent_bound N hN hell8)
    (computed_local_cell_budget N ((by decide : 1 ≤ (8 : ℕ)).trans hell8)) le_rfl)

end EditApproximation

end OAI
