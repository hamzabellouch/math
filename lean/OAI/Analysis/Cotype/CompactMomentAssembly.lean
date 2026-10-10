import OAI.Analysis.Cotype.CompactQuotient
import OAI.Analysis.Cotype.L2Sequence

namespace OAI

noncomputable section

open scoped BigOperators ENNReal
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (A : ℕ → Submodule ℝ X)

theorem moment_clm {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {m : ℕ}
    (T : Y →L[ℝ] Z) (f : Cube m → Y) (i : Fin m) :
    T (moment Y f i) = moment Z (fun ε => T (f ε)) i := by
  simp [moment, average]

theorem exists_levelSum_moment_lift {m : ℕ} {D : ℝ} (hD : 0 < D)
    (hL : ∀ l, FiniteLevelLift m D (A l) (A (l+1))) (z : Fin m → LevelSum A) :
    ∃ H : Cube m → LevelSum A,
      (∀ i, weightedMap A (moment (LevelSum A) H i) = weightedMap A (z i)) ∧
      cubeL2 (LevelSum A) H ≤ 6 * D * Real.sqrt (∑ i, ‖z i‖^2) := by
  classical
  choose L hLm hLn using (fun l => hL l (fun i => z i l))
  have hzsum : Summable (fun l => ∑ i, ‖z i l‖^2) := by
    have hs (s : Finset (Fin m)) : Summable (fun l => ∑ i ∈ s, ‖z i l‖^2) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih => simpa only [Finset.sum_insert hi] using (lp_two_summable_sq (z i)).add ih
    exact hs Finset.univ
  have hLsq (l : ℕ) : cubeL2 (A (l+1)) (L l)^2 ≤ (3*D)^2 * ∑ i, ‖z i l‖^2 := by
    have h := (sq_le_sq₀ (cubeL2_nonneg (L l)) (by positivity)).mpr (hLn l)
    simpa only [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i l‖))] using h
  have hLsum : Summable (fun l => cubeL2 (A (l+1)) (L l)^2) :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _) hLsq (hzsum.mul_left _)
  have hεsum (ε : Cube m) : Summable (fun l => ‖L l ε‖^2) :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _)
      (fun l => norm_sq_le_card_cubeL2_sq (L l) ε) (hLsum.mul_left _)
  let raw (ε : Cube m) : ∀ l, A l
    | 0 => 0
    | l+1 => (2 : ℝ) • L l ε
  have hraw (ε : Cube m) : Memℓp (raw ε) 2 := by
    apply mem_lp_two_of_summable_sq
    apply (summable_nat_add_iff 1).mp
    simpa [raw, norm_smul, mul_pow, show (2 : ℝ)^2 = 4 by norm_num] using (hεsum ε).mul_left 4
  let H : Cube m → LevelSum A := fun ε => ⟨raw ε, hraw ε⟩
  have hzero (i : Fin m) : (moment (LevelSum A) H i 0 : X) = 0 := by
    have he := moment_clm ((A 0).subtypeL.comp (lp.evalCLM ℝ (fun l => A l) 2 0)) H i
    change (moment (LevelSum A) H i 0 : X) = moment X (fun _ => 0) i at he
    simpa [moment, average] using he
  have hsucc (i : Fin m) (l : ℕ) :
      (moment (LevelSum A) H i (l+1) : X) = (2 : ℝ) • (z i l : X) := by
    have he := moment_clm ((A (l+1)).subtypeL.comp (lp.evalCLM ℝ (fun l => A l) 2 (l+1))) H i
    change (moment (LevelSum A) H i (l+1) : X) =
      moment X (fun ε => (2:ℝ) • (L l ε : X)) i at he
    rw [he]
    have hs : moment X (fun ε => (2:ℝ) • (L l ε : X)) i =
        (2 : ℝ) • moment X (fun ε => (L l ε : X)) i := by
      simp [moment, average, Finset.smul_sum, smul_smul, mul_comm, mul_left_comm]
    rw [hs, hLm]
  refine ⟨H, ?_, ?_⟩
  · intro i
    rw [weightedMap_apply, (weightedMap_summable_apply A (moment (LevelSum A) H i)).tsum_eq_zero_add]
    simp only [hzero, smul_zero, zero_add, hsucc]
    rw [weightedMap_apply]
    apply tsum_congr
    intro l
    rw [smul_smul]
    congr 1
    rw [pow_succ]
    ring
  · apply (sq_le_sq₀ (cubeL2_nonneg H) (by positivity)).mp
    rw [cubeL2_lp_sq]
    have he : (fun l => cubeL2 (A l) (fun ε => H ε l)^2) =
        fun l => match l with | 0 => 0 | k+1 => 4 * cubeL2 (A (k+1)) (L k)^2 := by
      funext l
      cases l with
      | zero => simp [H, raw, cubeL2_const]
      | succ l => norm_num [H, raw, cubeL2_smul, mul_pow]
    rw [he]
    have hs : Summable (fun l => match l with | 0 => (0:ℝ) | k+1 => 4 * cubeL2 (A (k+1)) (L k)^2) := by
      apply (summable_nat_add_iff 1).mp
      simpa using hLsum.mul_left 4
    rw [hs.tsum_eq_zero_add, zero_add, tsum_mul_left]
    have htotal : ∑' l, ∑ i, ‖z i l‖^2 = ∑ i, ‖z i‖^2 := by
      rw [Summable.tsum_finsetSum (fun i _ => lp_two_summable_sq (z i))]
      simp_rw [← lp_two_norm_sq]
    have hn := hLsum.tsum_le_tsum hLsq (hzsum.mul_left ((3*D)^2))
    rw [tsum_mul_left, htotal] at hn
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i‖))]
    nlinarith

end Cotype

end

end OAI
