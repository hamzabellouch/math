import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.MixedTrivializationBound
import OAI.Analysis.BiholderTransport.Geodesics.NormalEndpointLog
import OAI.Analysis.BiholderTransport.Calculus.MixedContinuity

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

lemma movingNormalEndpointJoinAction_chart_contDiffAt {a c x : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hy : riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hh : 0<h) (hh1 : h<1)
    (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingNormalEndpointJoinAction a c))
      ((h,((extChartAt 𝓘(ℝ,Model n) a) x,
        (extChartAt 𝓘(ℝ,Model n) c) (riemannianExp x p))),
       (0,(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)) := by
  apply movingNormalEndpointJoinAction_contDiffAt
    ((extChartAt 𝓘(ℝ,Model n) a).map_source hx)
    ((extChartAt 𝓘(ℝ,Model n) c).map_source hy) hh.ne' hh1.ne
  · rw [(extChartAt 𝓘(ℝ,Model n) c).left_inv hy,movingNormal_trivialization_exp hx]
  · rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx,tangent_symmL_trivialization hx]
    exact hleft
  · rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv hx,tangent_symmL_trivialization hx]
    exact hright

def movingEndpointFamily (a c : M) (r : ℝ×(Model n×(Model n×Model n)))
    (z : Model n×Model n) : ℝ :=
  movingNormalEndpointJoinAction a c (r.1,(r.2.1,r.2.2.1)) z

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma movingEndpointFamily_contDiffAt {a c : M} {h : ℝ}
    {q : Model n×(Model n×Model n)}
    (H : ContDiffAt ℝ ∞ (Function.uncurry (movingNormalEndpointJoinAction a c))
      ((h,(q.1,q.2.1)),(0,q.2.2))) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingEndpointFamily a c)) ((h,q),(0,q.2.2)) := by
  exact H.comp ((h,q),(0,q.2.2))
    ((contDiffAt_fst.fst.prodMk
      (contDiffAt_fst.snd.fst.prodMk contDiffAt_fst.snd.snd.fst)).prodMk contDiffAt_snd)

lemma compact_movingEndpointFamily_bound {a c : M} {h : ℝ} {K L : Set M}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKs : K⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hLs : L⊆(extChartAt 𝓘(ℝ,Model n) c).source)
    (hh : 0<h) (hh1 : h<1)
    (Hsplit : ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      h • p∈injectivityDomain x ∧
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∃ B>0, ∀ᶠ s in 𝓝 h, ∀ q∈minimizingEndpointChartParameters (n := n) a c K L,
      ContDiffAt ℝ 2 (movingEndpointFamily a c (s,q)) (0,q.2.2) ∧
      ‖fderiv ℝ (fderiv ℝ (movingEndpointFamily a c (s,q))) (0,q.2.2)‖≤B := by
  apply compact_parameter_second_jet_on_graph
    (isCompact_minimizingEndpointChartParameters hK hL hKs hLs)
    (v := fun q : Model n×(Model n×Model n) => (0,q.2.2))
    (continuous_const.prodMk continuous_snd.snd)
  intro q hq
  obtain ⟨z,hz,rfl⟩ := hq
  have hx := hKs hz.2.1
  have hy := hLs hz.2.2
  apply movingEndpointFamily_contDiffAt
  simp only [tangent_chart_trivialization hx]
  exact movingNormalEndpointJoinAction_chart_contDiffAt hx hy hh hh1
    (Hsplit z.1 z.2 hz.1).1 (Hsplit z.1 z.2 hz.1).2

lemma normalEndpointMixedOperator_bound_near_pair {h : ℝ} (hh : 0<h) (hh1 : h<1)
    (Hsplit : ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      h • p∈injectivityDomain x ∧
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a c : M) :
    ∃ C>0, ∃ U∈𝓝 (a,c), ∀ᶠ s in 𝓝 h,
      ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
        (x,riemannianExp x p)∈U → p∈minimizingVectors x →
          ‖normalEndpointMixedOperator x (riemannianExp x p) s p‖≤C := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨B,hBpos,hB⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) a
  obtain ⟨D,hDpos,hD⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c
  obtain ⟨K,hKn,hKs,hKc⟩ := local_compact_nhds
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) hB)
  obtain ⟨L,hLn,hLs,hLc⟩ := local_compact_nhds
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) c) hD)
  obtain ⟨E,hE,HE⟩ := compact_movingEndpointFamily_bound hKc hLc
    (fun x hx => (hKs hx).1) (fun y hy => (hLs hy).1) hh hh1 Hsplit
  refine ⟨E*D*B,mul_pos (mul_pos hE hDpos) hBpos,K×ˢL,prod_mem_nhds hKn hLn,?_⟩
  filter_upwards [HE] with s hs
  intro x p hxy hp
  have H := hs _ (trivialization_mem_minimizingEndpointChartParameters hxy.1
    (hKs hxy.1).1 hp hxy.2)
  exact (normalEndpointMixedOperator_norm_trivialization_le
    (hKs hxy.1).1 (hLs hxy.2).1 hBpos.le hDpos.le
    (hKs hxy.1).2.le (hLs hxy.2).2.le p H.1).trans (by
      change ‖fderiv ℝ (fderiv ℝ (movingEndpointFamily a c (s,_))) _‖*D*B≤E*D*B
      gcongr
      exact H.2)

lemma normalEndpointMixedOperator_uniform_bound {h : ℝ} (hh : 0<h) (hh1 : h<1)
    (Hsplit : ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x, p∈minimizingVectors x →
      h • p∈injectivityDomain x ∧
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∃ C>0, ∀ᶠ s in 𝓝 h, ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ‖normalEndpointMixedOperator x (riemannianExp x p) s p‖≤C := by
  classical
  have H := fun z : M×M => normalEndpointMixedOperator_bound_near_pair hh hh1 Hsplit z.1 z.2
  choose C hC U hU HU using H
  obtain ⟨S,hS⟩ := finite_cover_nhds hU
  let B := 1+∑ z∈S, |C z|
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  have HT := (eventually_all_finset S).mpr (fun a _ => HU a)
  filter_upwards [HT] with t ht
  intro x p hp
  have hx : (x,riemannianExp x p)∈ ⋃ a∈S,U a := by rw [hS]; trivial
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hx
  apply (ht a ha x p hxa hp).trans
  calc
    C a≤|C a| := le_abs_self _
    _≤∑ z∈S, |C z| := Finset.single_le_sum (fun z _ => abs_nonneg (C z)) ha
    _≤B := le_add_of_nonneg_left zero_le_one

end WeakMTWTransport

end

end OAI
