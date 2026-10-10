import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ManifoldLipschitz
import OAI.Analysis.BiholderTransport.Coordinates.ChartCostJets

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma compact_parameter_second_jet {K : Set Q} (hK : IsCompact K)
    {F : (ℝ×Q) → E → ℝ} {t : ℝ}
    (hF : ∀ q∈K, ContDiffAt ℝ ∞ (Function.uncurry F) ((t,q),0)) :
    ∃ B>0, ∀ᶠ s in 𝓝 t, ∀ q∈K,
      ContDiffAt ℝ 2 (F (s,q)) 0 ∧ ‖fderiv ℝ (fderiv ℝ (F (s,q))) 0‖≤B := by
  let H := fun z : ℝ×Q => fderiv ℝ (fderiv ℝ (F z)) 0
  have hH : ∀ q∈K, ContinuousAt H (t,q) := by
    intro q hq
    exact (ContDiffAt.partial_snd_fderiv_two (hF q hq)).continuousAt.comp
      (x := (t,q)) (f := fun z : ℝ×Q => (z,(0:E)))
      (continuousAt_id.prodMk continuousAt_const)
  obtain ⟨B,hB,HB⟩ := compact_eventually_fiberwise_bound hK
    (f := fun _ : Q => ()) continuous_const (g := fun _ : ℝ => ())
    (continuousAt_const (x := t)) (h := H) (fun q hq _ => hH q hq)
  have HS : ∀ᶠ s in 𝓝 t, ∀ q∈K, ()=() → ContDiffAt ℝ 2 (F (s,q)) 0 := by
    apply compact_eventually_fiberwise hK (f := fun _ : Q => ()) continuous_const
      (g := fun _ : ℝ => ()) (continuousAt_const (x := t))
    intro q hq _
    have He := ((hF q hq).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by simp)
    have hc : ContinuousAt (fun z : ℝ×Q => (z,(0:E))) (t,q) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hc.tendsto.eventually He] with z hz
    exact hz.comp (0:E) (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨B,hB,?_⟩
  filter_upwards [HB,HS] with s hb hs
  exact fun q hq => ⟨hs q hq rfl,hb q hq rfl⟩

end

open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def shortLegCost (x : M) (t : ℝ) (p h : TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  cost (riemannianExp x (t • (p+h))) (riemannianExp x p)

def movingShortLegCost (a : M) (z : ℝ × (Model n × Model n)) (h : Model n) : ℝ :=
  cost (movingNormal a (z.2.1,z.1 • (z.2.2+h))) (movingNormal a z.2)

lemma movingShortLegCost_contDiffAt {a : M} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingShortLegCost a)) ((1,(b,p)),0) := by
  let Z := (ℝ × (Model n × Model n)) × Model n
  have hA : ContMDiffAt 𝓘(ℝ,Z) 𝓘(ℝ,Model n) ∞
      (fun q : Z => movingNormal a (q.1.2.1,q.1.1 • (q.1.2.2+q.2))) ((1,(b,p)),0) := by
    refine (show ContMDiffAt 𝓘(ℝ,Model n × Model n) 𝓘(ℝ,Model n) ∞
      (movingNormal a) (b,(1:ℝ) • (p+0)) from by simpa using movingNormal_contMDiffAt hb).comp
      (f := fun q : Z => (q.1.2.1,q.1.1 • (q.1.2.2+q.2))) ((1,(b,p)),0) ?_
    exact (contDiffAt_fst.snd.fst.prodMk
      (contDiffAt_fst.fst.smul (contDiffAt_fst.snd.snd.add contDiffAt_snd))).contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,Z) 𝓘(ℝ,Model n) ∞
      (fun q : Z => movingNormal a q.1.2) ((1,(b,p)),0) :=
    (movingNormal_contMDiffAt (q := (b,p)) hb).comp ((1,(b,p)),0)
      contDiffAt_fst.snd.contMDiffAt
  have hC : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M × M => cost q.1 q.2)
      (movingNormal a (b,(1:ℝ) • (p+0)),movingNormal a (b,p)) := by
    simpa only [add_zero,one_smul,riemannianExp_zero] using
      cost_contMDiffAt_of_injectivityDomain
        (⟨movingNormal a (b,p),0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
        (zero_mem_injectivityDomain (movingNormal a (b,p)))
  exact (hC.comp ((1,(b,p)),0) (hA.prodMk hB)).contDiffAt

lemma shortLeg_second_bound_near_base (R : ℝ) (a : M) :
    ∃ C : ℝ≥0, ∃ K∈𝓝 a, ∀ᶠ t in 𝓝 (1:ℝ), ∀ x∈K,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) x, ‖p‖≤R →
      ContDiffAt ℝ 2 (shortLegCost x t p) 0 ∧
      ∀ k : TangentSpace 𝓘(ℝ,Model n) x,
      ‖fderiv ℝ (fderiv ℝ (shortLegCost x t p)) 0 k k‖≤C*‖k‖^2 := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨B,hBpos,hB⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) a
  obtain ⟨K,hKn,hKs,hKc⟩ := local_compact_nhds
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) hB)
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let P := (χ '' K) ×ˢ closedBall (0 : Model n) (B*R)
  have hPc : IsCompact P :=
    (hKc.image_of_continuousOn ((continuousOn_extChartAt a).mono
      (fun x hx => (hKs hx).1))).prod (isCompact_closedBall _ _)
  obtain ⟨D,hDpos,HD⟩ := compact_parameter_second_jet hPc
    (F := movingShortLegCost a) (t := 1) (fun q hq => movingShortLegCost_contDiffAt (by
      obtain ⟨x,hx,hxq⟩ := hq.1
      rw [←hxq]
      exact χ.map_source (hKs hx).1))
  refine ⟨⟨D*B^2,mul_nonneg hDpos.le (sq_nonneg B)⟩,K,hKn,?_⟩
  filter_upwards [HD] with t ht
  intro x hx p hp
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x
  have hpP : (χ x,A p)∈P := by
    refine ⟨mem_image_of_mem χ hx,?_⟩
    rw [mem_closedBall,dist_zero_right]
    exact (A.le_opNorm p).trans (mul_le_mul (hKs hx).2.le hp (norm_nonneg _) hBpos.le)
  have he : shortLegCost x t p = (fun h => movingShortLegCost a (t,(χ x,A p)) (A h)) := by
    funext h
    dsimp only [shortLegCost,movingShortLegCost]
    rw [←map_add,←map_smul,movingNormal_trivialization_exp (hKs hx).1,
      movingNormal_trivialization_exp (hKs hx).1]
  rw [he]
  have HD' := ht (χ x,A p) hpP
  refine ⟨(show ContDiffAt ℝ 2 (movingShortLegCost a (t,(χ x,A p))) (A 0) from by
    simpa only [map_zero] using HD'.1).comp 0 A.contDiff.contDiffAt,?_⟩
  intro k
  rw [second_fderiv_comp_linear_zero HD'.1 A k]
  let H := fderiv ℝ (fderiv ℝ (movingShortLegCost a (t,(χ x,A p)))) 0
  have hAk : ‖A k‖≤B*‖k‖ :=
    (A.le_opNorm k).trans (mul_le_mul_of_nonneg_right (hKs hx).2.le (norm_nonneg _))
  calc
    ‖H (A k) (A k)‖≤‖H (A k)‖*‖A k‖ := (H (A k)).le_opNorm _
    _≤(‖H‖*‖A k‖)*‖A k‖ := mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _)
    _≤(D*‖A k‖)*‖A k‖ := by gcongr; exact HD'.2
    _≤(D*(B*‖k‖))*(B*‖k‖) := by gcongr
    _=(D*B^2)*‖k‖^2 := by ring

lemma exists_uniform_shortLeg_second_bound (R : ℝ) :
    ∃ C : ℝ≥0, ∀ᶠ t in 𝓝 (1:ℝ), ∀ x : M,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) x, ‖p‖≤R →
      ContDiffAt ℝ 2 (shortLegCost x t p) 0 ∧
      ∀ k : TangentSpace 𝓘(ℝ,Model n) x,
      ‖fderiv ℝ (fderiv ℝ (shortLegCost x t p)) 0 k k‖≤C*‖k‖^2 := by
  classical
  choose C K hKn hK using shortLeg_second_bound_near_base (n := n) (M := M) R
  obtain ⟨s,hs⟩ := finite_cover_nhds hKn
  refine ⟨s.sup C,?_⟩
  have HT := (eventually_all_finset s).mpr (fun a _ => hK a)
  filter_upwards [HT] with t ht
  intro x p hp
  have hx : x∈ ⋃ a∈s,K a := by rw [hs]; trivial
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hx
  have H := ht a ha x hxa p hp
  refine ⟨H.1,fun k => (H.2 k).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.le_sup (f := C) ha) (sq_nonneg _)

end WeakMTWTransport

end

end OAI
