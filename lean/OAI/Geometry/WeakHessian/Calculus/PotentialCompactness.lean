import Mathlib
import OAI.Geometry.WeakHessian.Transport.QuadraticCostIncrement

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile15
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma exists_lipschitz_locally_uniform_subsequence
    (o : X) (L : ℝ≥0) (fs : ℕ → X → ℝ) (hLip : ∀ n, LipschitzWith L (fs n))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |fs n o| ≤ B) :
    ∃ f : X → ℝ, ∃ s : ℕ → ℕ, StrictMono s ∧ LipschitzWith L f ∧
      (∀ x, Tendsto (fun n => fs (s n) x) atTop (𝓝 (f x))) ∧
      ∀ k : ℕ, TendstoUniformlyOn (fun n => fs (s n)) f atTop
        (Metric.closedBall o (k:ℝ)) := by
  let Q (k : ℕ) := Metric.closedBall o (k:ℝ)
  let (k : ℕ) : CompactSpace (Q k) := isCompact_iff_compactSpace.mp (isCompact_closedBall o (k:ℝ))
  let vs (n k : ℕ) : C(Q k,ℝ) := ⟨fun x => fs n x,(hLip n).continuous.comp continuous_subtype_val⟩
  let M (k : ℕ) := B+(L:ℝ)*k
  let S (k : ℕ) := {f : C(Q k,ℝ) | LipschitzWith L f ∧ ‖f‖ ≤ M k}
  have hS (k : ℕ) : IsCompact (S k) :=
    WeakHessianTransport.isCompact_lipschitz_norm_ball L (by dsimp [M]; positivity)
  have hvs (n k : ℕ) : vs n k ∈ S k := by
    refine ⟨?_,?_⟩
    · change LipschitzWith L (fun x : Q k => fs n x)
      simpa only [mul_one,Function.comp_def] using (hLip n).comp (LipschitzWith.subtype_val (Q k))
    · apply (ContinuousMap.norm_le _ (by dsimp [M]; positivity)).mpr
      intro x
      have hl := (hLip n).dist_le_mul x o
      have hd : dist (x:X) o ≤ k := x.property
      have H : |fs n x| ≤ |fs n o|+|fs n x-fs n o| := by
        simpa only [Real.norm_eq_abs,abs_sub_comm] using norm_le_norm_add_norm_sub (fs n o) (fs n x)
      change ‖fs n x‖ ≤ _
      rw [Real.norm_eq_abs]
      exact H.trans (add_le_add (hb n) (by rw [← Real.dist_eq]; exact hl.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)))
  obtain ⟨F,hF,s,hs,ht⟩ := (isCompact_pi_infinite hS).tendsto_subseq (fun n => hvs n)
  have hk (k : ℕ) : Tendsto (fun n => vs (s n) k) atTop (𝓝 (F k)) :=
    (continuous_apply k).tendsto F |>.comp ht
  have hxk (k : ℕ) (x : Q k) : Tendsto (fun n => fs (s n) x) atTop (𝓝 (F k x)) :=
    (continuous_eval_const x).tendsto (F k) |>.comp (hk k)
  have hex (x : X) : ∃ k : ℕ, x ∈ Q k := by
    obtain ⟨k,hk⟩ := exists_nat_ge (dist x o)
    exact ⟨k,hk⟩
  let k (x : X) := (hex x).choose
  let f (x : X) := F (k x) ⟨x,(hex x).choose_spec⟩
  have hp (x : X) : Tendsto (fun n => fs (s n) x) atTop (𝓝 (f x)) := hxk (k x) _
  have he (j : ℕ) (x : Q j) : F j x = f x := tendsto_nhds_unique (hxk j x) (hp x)
  have hf : LipschitzWith L f := by
    apply isClosed_setOfPred_lipschitzWith L |>.mem_of_tendsto (tendsto_pi_nhds.mpr hp)
    exact Eventually.of_forall fun n => hLip (s n)
  refine ⟨f,s,hs,hf,hp,?_⟩
  intro j
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp (hk j)) ε hε] with n hn x hx
  have H := ContinuousMap.dist_apply_le_dist (f := vs (s n) j) (g := F j) ⟨x,hx⟩
  change dist (fs (s n) x) (F j ⟨x,hx⟩) ≤ _ at H
  rw [he] at H
  simpa only [dist_comm] using H.trans_lt hn
end WeakHessian

end
end InlinedFile15

end OAI
