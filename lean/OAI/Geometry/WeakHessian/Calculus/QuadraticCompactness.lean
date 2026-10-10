import Mathlib
import OAI.Geometry.WeakHessian.Transport.QuadraticCostIncrement
import OAI.Geometry.WeakHessian.Sobolev.QuadraticGradient

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile40
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma exists_quadratic_locally_uniform_subsequence
    (o : X) (R : ℝ≥0) (fs : ℕ → X → ℝ)
    (hLip : ∀ n, QuadraticLipschitzBound o R (fs n))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |fs n o| ≤ B) :
    ∃ f : X → ℝ, ∃ s : ℕ → ℕ, StrictMono s ∧ QuadraticLipschitzBound o R f ∧
      (∀ x, Tendsto (fun n => fs (s n) x) atTop (𝓝 (f x))) ∧
      ∀ k : ℕ, TendstoUniformlyOn (fun n => fs (s n)) f atTop
        (Metric.closedBall o (k:ℝ)) := by
  let Q (k : ℕ) := Metric.closedBall o (k:ℝ)
  let (k : ℕ) : CompactSpace (Q k) := isCompact_iff_compactSpace.mp (isCompact_closedBall o (k:ℝ))
  let vs (n k : ℕ) : C(Q k,ℝ) := ⟨fun x => fs n x,((hLip n).continuous R.coe_nonneg).comp continuous_subtype_val⟩
  let L (k : ℕ) : ℝ≥0 := k+R
  let M (k : ℕ) := B+(L k:ℝ)*k
  let S (k : ℕ) := {f : C(Q k,ℝ) | LipschitzWith (L k) f ∧ ‖f‖ ≤ M k}
  have hS (k : ℕ) : IsCompact (S k) :=
    WeakHessianTransport.isCompact_lipschitz_norm_ball (L k) (by dsimp [M]; positivity)
  have hvs (n k : ℕ) : vs n k ∈ S k := by
    refine ⟨?_,?_⟩
    · change LipschitzWith (L k) (fun x : Q k => fs n x)
      apply LipschitzWith.of_dist_le_mul
      intro x y
      have H := ((hLip n).lipschitzOn_ball R.coe_nonneg o (k:ℝ≥0)).dist_le_mul x x.property y y.property
      simpa only [dist_self,zero_add,add_zero,NNReal.coe_mk,NNReal.coe_add,NNReal.coe_natCast,L,add_comm,Subtype.dist_eq] using H
    · apply (ContinuousMap.norm_le _ (by dsimp [M]; positivity)).mpr
      intro x
      have hl := (hLip n).lipschitzOn_ball R.coe_nonneg o (k:ℝ≥0) |>.dist_le_mul x x.property o (by simp)
      have hl : dist (fs n x) (fs n o) ≤ (L k:ℝ)*dist (x:X) o := by
        simpa only [dist_self,zero_add,add_zero,NNReal.coe_mk,NNReal.coe_add,NNReal.coe_natCast,L,add_comm] using hl
      have hd : dist (x:X) o ≤ k := x.property
      have H : |fs n x| ≤ |fs n o|+|fs n x-fs n o| := by
        simpa only [Real.norm_eq_abs,abs_sub_comm] using norm_le_norm_add_norm_sub (fs n o) (fs n x)
      change ‖fs n x‖ ≤ _
      rw [Real.norm_eq_abs]
      exact H.trans (add_le_add (hb n) (by rw [← Real.dist_eq]; exact hl.trans (mul_le_mul_of_nonneg_left hd (L k).coe_nonneg)))
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
  have hf : QuadraticLipschitzBound o R f := by
    intro x y
    exact le_of_tendsto_of_tendsto' ((hp x).sub (hp y) |>.abs) tendsto_const_nhds
      (fun n => hLip (s n) x y)
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
end InlinedFile40

end OAI
