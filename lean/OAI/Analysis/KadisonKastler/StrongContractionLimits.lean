import OAI.Analysis.KadisonKastler.StrongCommutantTests
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Topology.MetricSpace.Cauchy

namespace OAI

/-! # Recovering a strong contraction limit from countable coordinates -/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem cauchySeq_apply_of_dense_contractions (ξ : ℕ → H) (hξ : DenseRange ξ)
    (A : ℕ → H →L[ℂ] H) (hA : ∀ n, ‖A n‖ ≤ 1)
    (h : ∀ j, CauchySeq (fun n => A n (ξ j))) (x : H) :
    CauchySeq (fun n => A n x) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := hξ.exists_dist_lt x (by positivity : 0 < ε / 4)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (h j) (ε / 2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hdist (k : ℕ) (u v : H) : dist (A k u) (A k v) ≤ dist u v := by
    simp only [dist_eq_norm, ← map_sub]
    exact ((A k).le_opNorm (u - v)).trans
      (by simpa using mul_le_mul_of_nonneg_right (hA k) (norm_nonneg (u - v)))
  have hleft := hdist m x (ξ j)
  have hright := hdist n (ξ j) x
  have hmid := hN m hm n hn
  have ht := (dist_triangle (A m x) (A m (ξ j)) (A n x)).trans
    (add_le_add le_rfl (dist_triangle (A m (ξ j)) (A n (ξ j)) (A n x)))
  rw [dist_comm (ξ j) x] at hright
  linarith

variable [CompleteSpace H]

/-- No convergence is assumed away from the fixed dense sequence. -/
theorem exists_strong_limit_of_dense_contractions (ξ : ℕ → H) (hξ : DenseRange ξ)
    (A : ℕ → H →L[ℂ] H) (hA : ∀ n, ‖A n‖ ≤ 1)
    (h : ∀ j, CauchySeq (fun n => A n (ξ j))) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ 1 ∧
      ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (T x)) := by
  have hc (x : H) := cauchySeq_apply_of_dense_contractions ξ hξ A hA h x
  choose f hf using fun x => cauchy_map_iff_exists_tendsto.mp (hc x)
  have hb (x : H) : ‖f x‖ ≤ ‖x‖ := by
    apply le_of_tendsto (hf x).norm
    exact Eventually.of_forall fun n => ((A n).le_opNorm x).trans
      (by simpa using mul_le_mul_of_nonneg_right (hA n) (norm_nonneg x))
  let L : H →ₗ[ℂ] H :=
    { toFun := f
      map_add' := fun x y => by
        have ht := (hf x).add (hf y)
        simp only [← map_add] at ht
        exact tendsto_nhds_unique (hf (x + y)) ht
      map_smul' := fun c x => by
        have ht := (hf x).const_smul c
        simp only [← map_smul] at ht
        exact tendsto_nhds_unique (hf (c • x)) ht }
  have hL (x : H) : ‖L x‖ ≤ 1 * ‖x‖ := by
    change ‖f x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using hb x
  let T := L.mkContinuous 1 hL
  refine ⟨T, T.opNorm_le_bound zero_le_one (fun x => ?_), hf⟩
  change ‖f x‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using hb x

omit [CompleteSpace H] in
/-- Uniform contraction bounds permit a varying input vector. -/
theorem tendsto_apply_contractions {ι : Type*} {l : Filter ι}
    (A : ι → H →L[ℂ] H) (T : H →L[ℂ] H) (hA : ∀ i, ‖A i‖ ≤ 1)
    (hT : ∀ x, Tendsto (fun i => A i x) l (𝓝 (T x)))
    {x : ι → H} {y : H} (hx : Tendsto x l (𝓝 y)) :
    Tendsto (fun i => A i (x i)) l (𝓝 (T y)) := by
  have hz : Tendsto (fun i => A i (x i - y)) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_) (by simpa using (hx.sub_const y).norm)
    exact ((A i).le_opNorm _).trans
      (by simpa using mul_le_mul_of_nonneg_right (hA i) (norm_nonneg (x i - y)))
  convert hz.add (hT y) using 1 <;> simp

omit [CompleteSpace H] in
theorem tendsto_mul_contractions {ι : Type*} {l : Filter ι}
    (A B : ι → H →L[ℂ] H) (T S : H →L[ℂ] H) (hA : ∀ i, ‖A i‖ ≤ 1)
    (hT : ∀ x, Tendsto (fun i => A i x) l (𝓝 (T x)))
    (hS : ∀ x, Tendsto (fun i => B i x) l (𝓝 (S x))) (x : H) :
    Tendsto (fun i => (A i * B i) x) l (𝓝 ((T * S) x)) :=
  tendsto_apply_contractions A T hA hT (hS x)

end

end KadisonKastler

end OAI
