import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MovingCrossing
import OAI.Analysis.BiholderTransport.Geodesics.MinimizingChartParameters
import OAI.Analysis.BiholderTransport.Volume.UniformExpJacobian

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma fixedJoinMiddle_interval_crossing_near_base {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (Hsplit : ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      h • p∈injectivityDomain x ∧
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) (a : M) :
    ∃ c > 0, ∃ C > 0, ∃ K∈𝓝 a, ∀ᶠ z in 𝓝 ((1:ℝ),(1:ℝ)), h < z.1 → z.2 < 1 → z.1 ≤ z.2 →
      ∀ x∈K, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      ∀ k : TangentSpace 𝓘(ℝ,Model n) x,
        c*(z.2-z.1)*‖k‖^2 ≤ fixedJoinMiddle x h z.1 p k k-fixedJoinMiddle x h z.2 p k k ∧
        fixedJoinMiddle x h z.1 p k k-fixedJoinMiddle x h z.2 p k k ≤ C*(z.2-z.1)*‖k‖^2 := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨B,hBpos,hB⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) a
  obtain ⟨D,hDpos,hD⟩ := eventually_norm_symmL_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) a
  obtain ⟨K,hKn,hKs,hKc⟩ := local_compact_nhds
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) (inter_mem hB hD))
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let e := trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  let P := minimizingChartParameters (n := n) a K
  have HP : ∀ q∈P, q.1∈χ.target ∧
      h • e.symmL ℝ (χ.symm q.1) q.2∈injectivityDomain (χ.symm q.1) ∧
      (1-h) • (sprayFlow h (⟨χ.symm q.1,e.symmL ℝ (χ.symm q.1) q.2⟩ :
        TangentBundle 𝓘(ℝ,Model n) M)).2∈injectivityDomain
        (sprayFlow h (⟨χ.symm q.1,e.symmL ℝ (χ.symm q.1) q.2⟩ :
          TangentBundle 𝓘(ℝ,Model n) M)).1 := by
    intro q hq
    have H := mem_minimizingChartParameters (fun x hx => (hKs hx).1) hq
    exact ⟨H.1,Hsplit _ _ H.2.2⟩
  obtain ⟨c,hc,C,hC,ε,hε,HC⟩ := compact_bilinear_interval_crossing
    (isCompact_minimizingChartParameters hKc (fun x hx => (hKs hx).1))
    (H := movingFixedJoinMiddle a h)
    (fun q hq => movingFixedJoinMiddle_contDiffAt
      (movingFixedJoinAction_contDiffAt (HP q hq).1 hh1.ne' (HP q hq).2.1 (HP q hq).2.2))
    (fun q hq v hv => movingFixedJoinMiddle_strict_crossing (HP q hq).1 hh hh1
      (HP q hq).2.1 (HP q hq).2.2 v hv)
  refine ⟨c/D^2,div_pos hc (sq_pos_of_pos hDpos),C*B^2,
    mul_pos hC (sq_pos_of_pos hBpos),K,hKn,?_⟩
  have Hz₁ : ∀ᶠ z : ℝ×ℝ in 𝓝 (1,1), z.1∈Metric.ball 1 ε :=
    continuousAt_fst.eventually (Metric.ball_mem_nhds 1 hε)
  have Hz₂ : ∀ᶠ z : ℝ×ℝ in 𝓝 (1,1), z.2∈Metric.ball 1 ε :=
    continuousAt_snd.eventually (Metric.ball_mem_nhds 1 hε)
  filter_upwards [Hz₁,Hz₂] with z hz₁ hz₂
  intro hhT hT1 hzle x hx p hp k
  let A := e.continuousLinearMapAt ℝ x
  have hxp : (χ x,A p)∈P :=
    trivialization_mem_minimizingChartParameters (fun x hx => (hKs hx).1) hx hp
  have HE := HC z.1 z.2 hz₁ hz₂ hzle (χ x,A p) hxp (A k)
  have HS := Hsplit x p hp
  have HB1 := (fixedJoinAction_shortened_contDiffAt hh1 (hhT.trans_le hzle) hT1 HS.1 HS.2).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HBT := (fixedJoinAction_shortened_contDiffAt hh1 hhT (hzle.trans_lt hT1) HS.1 HS.2).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [movingFixedJoinMiddle_trivialization (hKs hx).1 h z.1 p k k HBT,
    movingFixedJoinMiddle_trivialization (hKs hx).1 h z.2 p k k HB1] at HE
  have hbase : x∈e.baseSet := by
    simpa only [e,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (hKs hx).1
  have hA : ‖A k‖ ≤ B*‖k‖ :=
    (A.le_opNorm k).trans (mul_le_mul_of_nonneg_right (hKs hx).2.1.le (norm_nonneg _))
  have hL : ‖k‖ ≤ D*‖A k‖ := by
    calc
      ‖k‖ = ‖e.symmL ℝ x (A k)‖ := by rw [Trivialization.symmL_continuousLinearMapAt e hbase]
      _ ≤ ‖e.symmL ℝ x‖*‖A k‖ := (e.symmL ℝ x).le_opNorm _
      _ ≤ D*‖A k‖ := mul_le_mul_of_nonneg_right (hKs hx).2.2.le (norm_nonneg _)
  have hL2 : ‖k‖^2 ≤ D^2*‖A k‖^2 := by nlinarith only [hL,sq_nonneg (‖k‖-D*‖A k‖),norm_nonneg k,mul_nonneg hDpos.le (norm_nonneg (A k))]
  have hA2 : ‖A k‖^2 ≤ B^2*‖k‖^2 := by nlinarith only [hA,sq_nonneg (‖A k‖-B*‖k‖),norm_nonneg (A k),mul_nonneg hBpos.le (norm_nonneg k)]
  constructor
  · calc
      (c/D^2)*(z.2-z.1)*‖k‖^2 ≤ (c/D^2)*(z.2-z.1)*(D^2*‖A k‖^2) := by gcongr
      _ = c*(z.2-z.1)*‖A k‖^2 := by field_simp
      _ ≤ _ := HE.1
  · calc
      _ ≤ C*(z.2-z.1)*‖A k‖^2 := HE.2
      _ ≤ C*(z.2-z.1)*(B^2*‖k‖^2) := by gcongr
      _ = (C*B^2)*(z.2-z.1)*‖k‖^2 := by ring

lemma fixedJoinMiddle_uniform_interval_crossing {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (Hsplit : ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      h • p∈injectivityDomain x ∧
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ z in 𝓝 ((1:ℝ),(1:ℝ)), h < z.1 → z.2 < 1 → z.1 ≤ z.2 →
      ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      ∀ k : TangentSpace 𝓘(ℝ,Model n) x,
        c*(z.2-z.1)*‖k‖^2 ≤ fixedJoinMiddle x h z.1 p k k-fixedJoinMiddle x h z.2 p k k ∧
        fixedJoinMiddle x h z.1 p k k-fixedJoinMiddle x h z.2 p k k ≤ C*(z.2-z.1)*‖k‖^2 := by
  classical
  choose c hc C hC K hKn hK using fixedJoinMiddle_interval_crossing_near_base hh hh1 Hsplit
  obtain ⟨s,hs⟩ := finite_cover_nhds hKn
  have hlow : ∃ b > 0, ∀ a∈s, b ≤ c a := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨b,hb,Hb⟩ := ih
      refine ⟨min b (c a),lt_min hb (hc a),?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl|hz
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (Hb z hz)
  have hupp : ∃ b > 0, ∀ a∈s, C a ≤ b := by
    clear hs hlow
    induction s using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨b,hb,Hb⟩ := ih
      refine ⟨max b (C a),hb.trans_le (le_max_left _ _),?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl|hz
      · exact le_max_right _ _
      · exact (Hb z hz).trans (le_max_left _ _)
  obtain ⟨b,hb,Hb⟩ := hlow
  obtain ⟨B,hB,HB⟩ := hupp
  refine ⟨b,hb,B,hB,?_⟩
  have HT := (eventually_all_finset s).mpr (fun a _ => hK a)
  filter_upwards [HT] with z hT
  intro hhT hT1 hzle x p hp k
  have hx : x∈ ⋃ a∈s,K a := by rw [hs]; trivial
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hx
  have H := hT a ha hhT hT1 hzle x hxa p hp k
  refine ⟨le_trans ?_ H.1,le_trans H.2 ?_⟩
  · gcongr; exact Hb a ha
  · gcongr; exact HB a ha

end WeakMTWTransport

end

end OAI
