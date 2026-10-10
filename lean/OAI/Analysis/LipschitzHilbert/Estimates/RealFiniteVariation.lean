import OAI.Analysis.LipschitzHilbert.Estimates.RelativePartitionVariation
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteVariation

namespace OAI

/-! Real-valued finite variation and cancellation of the running radius
in the pathwise relative-exit estimate. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert
variable {Ω : Type*}

abbrev realVariationCube (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) : ℝ :=
  finiteCubicVariation (fun n => F n x) N

theorem realVariationCube_nonneg (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    0≤realVariationCube F N x := finiteCubicVariation_nonneg _ _

theorem partition_le_realVariationCube (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω)
    (p : Fin (N+1) → Fin (N+1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) x-F (p i.castSucc) x‖^3)≤realVariationCube F N x :=
  partition_le_finiteCubicVariation (E:=ℝ) (fun n => F n x) N p hp

theorem realVariationCube_relative_bound (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    realVariationCube F N x≤2048*runningOscillation F N x*weightedRelativeExitEnergy F (N+1) x := by
  classical
  unfold realVariationCube finiteCubicVariation
  apply Finset.sup'_le _
  intro p _
  split_ifs with hp
  · exact relative_partition_cube_bound F N x p hp
  · exact mul_nonneg (mul_nonneg (by norm_num) (runningOscillation_nonneg F N x))
      (weightedRelativeExitEnergy_nonneg F (N+1) x)

theorem initial_jump_le_realVariationCube (F : ℕ → Ω → ℝ) (N k : ℕ) (hk : k≤N) (x : Ω) :
    ‖F k x-F 0 x‖^3≤realVariationCube F N x := by
  classical
  by_cases hN : N=0
  · have hk0 : k=0 := by omega
    simpa [hk0] using realVariationCube_nonneg F N x
  have hNpos : 0<N := Nat.pos_of_ne_zero hN
  let p : Fin (N+1) → Fin (N+1) := fun i => if i.val=0 then 0 else ⟨k,Nat.lt_succ_of_le hk⟩
  have hp : Monotone p := by
    intro i j hij
    dsimp [p]
    split_ifs with hi hj
    · exact le_rfl
    · exact Fin.zero_le _
    · have : j.val≠0 := by intro hj; have := hij; change i.val≤j.val at this; omega
      contradiction
    · exact le_rfl
  have hterm : (∑ i : Fin N, ‖F (p i.succ) x-F (p i.castSucc) x‖^3)≥‖F k x-F 0 x‖^3 := by
    have h := Finset.single_le_sum (f:=fun i : Fin N => ‖F (p i.succ) x-F (p i.castSucc) x‖^3)
      (fun i _ => pow_nonneg (norm_nonneg _) _) (Finset.mem_univ (⟨0,hNpos⟩:Fin N))
    simpa [p] using h
  exact hterm.trans (partition_le_realVariationCube F N x p hp)

theorem runningOscillation_cube_le (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    runningOscillation F N x^3≤realVariationCube F N x := by
  obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    (fun i => |F i x-F 0 x|)
  change (Finset.range (N+1)).sup' Finset.nonempty_range_add_one (fun i => |F i x-F 0 x|)^3≤_
  rw [he]
  simpa only [Real.norm_eq_abs] using initial_jump_le_realVariationCube F N k (by simpa using hk) x

theorem cubic_radius_cancel (V R W : ℝ) (hV : 0≤V) (hR : 0≤R) (hW : 0≤W)
    (h1 : V≤2048*R*W) (h2 : R^3≤V) : V^(2/3:ℝ)≤2048*W := by
  let v := V^(1/3:ℝ)
  have hv : 0≤v := Real.rpow_nonneg hV _
  have hv3 : v^3=V := by
    dsimp [v]
    rw [←Real.rpow_natCast,←Real.rpow_mul hV]
    norm_num
  have hv2 : v^2=V^(2/3:ℝ) := by
    dsimp [v]
    rw [←Real.rpow_natCast,←Real.rpow_mul hV]
    norm_num
  have hRv : R≤v := by
    by_contra hn
    have hlt : v<R := lt_of_not_ge hn
    have hc : v^3<R^3 := (pow_lt_pow_iff_left₀ hv hR (by decide : (3:ℕ)≠0)).2 hlt
    linarith
  by_cases hv0 : v=0
  · rw [←hv2,hv0]
    norm_num
    exact hW
  have hvp : 0<v := lt_of_le_of_ne hv (Ne.symm hv0)
  have h3 := mul_le_mul_of_nonneg_right hRv (mul_nonneg (by norm_num : (0:ℝ)≤2048) hW)
  rw [←hv2]
  by_contra hn
  have hbad := mul_pos hvp (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith

theorem realVariationCube_two_thirds_bound (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    realVariationCube F N x^(2/3:ℝ)≤2048*weightedRelativeExitEnergy F (N+1) x :=
  cubic_radius_cancel _ _ _ (realVariationCube_nonneg F N x) (runningOscillation_nonneg F N x)
    (weightedRelativeExitEnergy_nonneg F (N+1) x) (realVariationCube_relative_bound F N x)
    (runningOscillation_cube_le F N x)

end LipschitzHilbert

end

end OAI
