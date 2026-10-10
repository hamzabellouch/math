import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.CompactSmoothGrowth
import OAI.Analysis.BiholderTransport.Convexity.EnvelopeData
import OAI.Analysis.BiholderTransport.LinearAlgebra.ScaledSlack

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

abbrev chartFiberInverse (a : M) (b : Model n) :=
  (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
    ((extChartAt 𝓘(ℝ,Model n) a).symm b)

omit [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartFiberInverse_injective {a : M} {b : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target) :
    Function.Injective (chartFiberInverse a b) := by
  let e := trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  have hx : (extChartAt 𝓘(ℝ,Model n) a).symm b ∈ e.baseSet := by
    simpa only [e,TangentBundle.trivializationAt_baseSet,extChartAt_source] using
      (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  rw [show (chartFiberInverse a b : Model n → _) =
      (e.continuousLinearEquivAt ℝ _ hx).symm from (e.symm_continuousLinearEquivAt_eq hx).symm]
  exact (e.continuousLinearEquivAt ℝ _ hx).symm.injective

lemma scaledNormalEnvelope_mean {ι : Type*} [Fintype ι]
    {a : M} {s : ℝ} (hs : s ≠ 0) {q : EnvelopeData (Model n) ι}
    (hb : q.1.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : chartFiberInverse a q.1.1 (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) ∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1))
    (hi : ∀ i, chartFiberInverse a q.1.1 (s • q.1.2 i) ∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1))
    (hsum : ∑ i, q.2.1 i = 1) (v : Model n) :
    ∑ i, q.2.1 i * fderiv ℝ (scaledNormalEnvelope a s q i) 0 v = 0 := by
  let L := chartFiberInverse a q.1.1
  let r := ∑ j, q.2.1 j • q.1.2 j
  have he : (∑ i, q.2.1 i • L (q.1.2 i-r)) = 0 := by
    simp only [map_sub,smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul,hsum,one_smul]
    rw [show (∑ i, q.2.1 i • L (q.1.2 i)) = L r by simp only [r,map_sum,map_smul]]
    exact sub_self _
  calc
    _ = q.2.2 * inner ℝ (∑ i, q.2.1 i • L (q.1.2 i-r)) (L v) := by
      simp only [scaledNormalEnvelope_first hs _ hb hp (hi _),sum_inner,
        real_inner_smul_left,Finset.mul_sum,L,r]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [he,inner_zero_left,mul_zero]

lemma WeakMTW.compact_scaled_envelope_growth
    (hmtw : WeakMTW (n := n) (M := M))
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : M) (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (d : P → EnvelopeData (Model n) ι) (hd : Continuous d)
    (hb : ∀ z, (d z).1.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hw : ∀ z i, 0 ≤ (d z).2.1 i) (hsum : ∀ z, ∑ i, (d z).2.1 i = 1)
    (ht : ∀ z, 0 ≤ (d z).2.2) (hts : ∀ z, (d z).2.2 < s)
    (hmin : ∀ z i, chartFiberInverse a (d z).1.1 ((d z).1.2 i) ∈
      minimizingVectors ((extChartAt 𝓘(ℝ,Model n) a).symm (d z).1.1))
    (hID : ∀ z p, p ∈ convexHull ℝ (range (fun i => chartFiberInverse a (d z).1.1 ((d z).1.2 i))) →
      (d z).2.2 • p ∈ injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (d z).1.1)) :
    ∃ b > 0, ∀ᶠ h : Model n in 𝓝 0, ∀ z : P, ∃ i,
      b * ‖h‖^2 ≤ scaledNormalEnvelope a s (d z) i h := by
  have hi : ∀ z i, chartFiberInverse a (d z).1.1 (s • (d z).1.2 i) ∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (d z).1.1) := by
    intro z i
    rw [map_smul]
    exact contracted_minimizer_mem_injectivityDomain (hmin z i) hs hs1
  have hp : ∀ z, chartFiberInverse a (d z).1.1 ((d z).2.2 • ∑ j, (d z).2.1 j • (d z).1.2 j) ∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (d z).1.1) := by
    intro z
    simp only [map_smul,map_sum]
    apply hID z
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hw z i) (hsum z)
      (fun i _ => subset_convexHull ℝ _ (mem_range_self i))
  apply compact_smooth_data_transverse_growth (scaledNormalEnvelope a s) d hd
    (fun z => (d z).2.1) hw hsum
  · intro i
    exact (continuous_apply i).comp hd.snd.fst
  · intro z i
    exact scaledNormalEnvelope_contDiffAt i (hb z) (hp z) (hi z i)
  · intro z i
    exact scaledNormalEnvelope_zero a s (d z) i
  · intro z v
    exact scaledNormalEnvelope_mean hs.ne' (hb z) (hp z) (hi z) (hsum z) v
  · intro z v hv hle
    let L := chartFiberInverse a (d z).1.1
    have hLv : L v ≠ 0 := by
      intro he
      have hv0 : v = 0 := (chartFiberInverse_injective (hb z)) (he.trans (map_zero L).symm)
      simp only [hv0,norm_zero] at hv
      norm_num at hv
    have H := hmtw.finite_scaled_transverse_positive
      (fun i => L ((d z).1.2 i)) ((d z).2.1) (hw z) (hsum z) (hmin z)
      (ht z) (hts z) hs1 (hID z) hLv
    have hl : ∀ i, (d z).2.2 * inner ℝ
        (L ((d z).1.2 i) - ∑ j, (d z).2.1 j • L ((d z).1.2 j)) (L v) ≤ 0 := by
      intro i
      simpa only [scaledNormalEnvelope_first hs.ne' i (hb z) (hp z) (hi z i),
        map_sub,map_sum,map_smul,L] using hle i
    have HH := H hl
    simpa only [scaledNormalEnvelope_second _ (hb z) (hp z) (hi z _),
      map_smul,map_sum,L] using HH

end WeakMTWTransport

end

end OAI
