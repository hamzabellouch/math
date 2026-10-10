import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

theorem seminorm_linearMap_le_of_sign_vertices {n : ℕ}
    (p : Seminorm ℝ E) (T : (Fin n → ℝ) →ₗ[ℝ] E) {K : ℝ}
    (hvertex : ∀ ε : Fin n → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) → p (T ε) ≤ K)
    (a : Fin n → ℝ) (ha : ∀ i, |a i| ≤ 1) : p (T a) ≤ K := by
  have hconv : Convex ℝ {b : Fin n → ℝ | p (T b) ≤ K} := by
    intro b hb c hc u v hu hv huv
    change p (T (u • b + v • c)) ≤ K
    rw [map_add, map_smul, map_smul]
    calc
      p (u • T b + v • T c) ≤ p (u • T b) + p (v • T c) := p.add_le' _ _
      _ = u * p (T b) + v * p (T c) := by
        rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hu, abs_of_nonneg hv]
      _ ≤ u * K + v * K := add_le_add
        (mul_le_mul_of_nonneg_left hb hu) (mul_le_mul_of_nonneg_left hc hv)
      _ = K := by rw [← add_mul, huv, one_mul]
  have hsubset : Set.univ.pi (fun _ : Fin n => ({-1, 1} : Set ℝ)) ⊆
      {b : Fin n → ℝ | p (T b) ≤ K} := by
    intro ε hε
    apply hvertex ε
    intro i
    have hi := hε i (Set.mem_univ i)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hi
  have hmem : a ∈ convexHull ℝ (Set.univ.pi (fun _ : Fin n => ({-1, 1} : Set ℝ))) := by
    apply mem_convexHull_pi
    intro i _
    rw [convexHull_pair, segment_eq_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
    exact abs_le.mp (ha i)
  exact convexHull_min hsubset hconv hmem

theorem seminorm_linearMap_le_mul_norm_of_sign_vertices {n : ℕ}
    (p : Seminorm ℝ E) (T : (Fin n → ℝ) →ₗ[ℝ] E) {K : ℝ}
    (_hK : 0 ≤ K)
    (hvertex : ∀ ε : Fin n → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) → p (T ε) ≤ K)
    (a : Fin n → ℝ) : p (T a) ≤ K * ‖a‖ := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  let b : Fin n → ℝ := ‖a‖⁻¹ • a
  have hb (i : Fin n) : |b i| ≤ 1 := by
    change |‖a‖⁻¹ * a i| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr ha)]
    calc
      ‖a‖⁻¹ * |a i| ≤ ‖a‖⁻¹ * ‖a‖ :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm a i)
          (inv_nonneg.mpr ha.le)
      _ = 1 := inv_mul_cancel₀ ha.ne'
  have hbound := seminorm_linearMap_le_of_sign_vertices p T hvertex b hb
  have hab : ‖a‖ • b = a := by
    dsimp only [b]
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  calc
    p (T a) = p (T (‖a‖ • b)) := congrArg (fun z => p (T z)) hab.symm
    _ = ‖a‖ * p (T b) := by
      rw [map_smul, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ha]
    _ ≤ ‖a‖ * K := mul_le_mul_of_nonneg_left hbound ha.le
    _ = K * ‖a‖ := mul_comm _ _

end MarkovSuperreflexivity

end

end OAI
