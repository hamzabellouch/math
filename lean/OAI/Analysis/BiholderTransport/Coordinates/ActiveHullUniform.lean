import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ActiveUniformGrowth
import OAI.Analysis.BiholderTransport.Regularity.FiniteSimplexRepresentation

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

section
omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma movingNormal_chart {a x : M} (hx : x ∈ (extChartAt 𝓘(ℝ,Model n) a).source)
    (p : TangentSpace 𝓘(ℝ,Model n) x) :
    movingNormal a (extChartAt 𝓘(ℝ,Model n) a x,
      tangentCoordChange 𝓘(ℝ,Model n) x a x p) = riemannianExp x p := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  have hs : (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) ∈ χ.source :=
    (tangent_chart_source_iff _ _).mpr hx
  change riemannianExp (χ.symm (χ ⟨x,p⟩)).1 (χ.symm (χ ⟨x,p⟩)).2 = _
  rw [χ.left_inv hs]

lemma movingNormal_trivialization {a x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ,Model n) a).source)
    (p : TangentSpace 𝓘(ℝ,Model n) x) :
    movingNormal a (extChartAt 𝓘(ℝ,Model n) a x,
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p) =
        riemannianExp x p := by
  have hx' : x ∈ (chartAt (Model n) a).source := by simpa only [extChartAt_source] using hx
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx']
  exact movingNormal_chart hx p

end

lemma WeakMTW.active_hull_uniform_strict_growth
    (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a : M} {K : Set M} (hK : IsCompact K)
    (hKa : K ⊆ (extChartAt 𝓘(ℝ,Model n) a).source)
    {T : ℝ} (hT : T < 1)
    (hID : ∀ x ∈ K, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      ∀ t ∈ Icc (0:ℝ) T, t • p ∈ injectivityDomain x) :
    ∀ᶠ h : Model n in 𝓝 0, ∀ x ∈ K,
      ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), ∀ t ∈ Icc (0:ℝ) T,
      h ≠ 0 →
      0 < t * (cTransform v (movingNormal a (extChartAt 𝓘(ℝ,Model n) a x,h)) - cTransform v x) +
        cost (movingNormal a (extChartAt 𝓘(ℝ,Model n) a x,h)) (riemannianExp x (t • p)) -
        cost x (riemannianExp x (t • p)) := by
  classical
  let k := Module.finrank ℝ (Model n) + 1
  have H : ∀ᶠ h : Model n in 𝓝 0, ∀ m ∈ Finset.Icc 1 k,
      ∀ q ∈ activeConfiguration v a K T (Fin m), h ≠ 0 →
        0 < q.2.2 * (cTransform v (movingNormal a (q.1.1,h)) -
            cTransform v ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) +
          movingNormalCost a q.1.1 (q.2.2 • ∑ i, q.2.1 i • q.1.2 i) h -
          movingNormalCost a q.1.1 (q.2.2 • ∑ i, q.2.1 i • q.1.2 i) 0 := by
    rw [Filter.eventually_all_finset]
    intro m hm
    have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
    let : Nonempty (Fin m) := ⟨⟨0,hm0⟩⟩
    obtain ⟨b,hb,Hb⟩ := hmtw.active_configurations_uniform_growth
      (ι := Fin m) hv hK hKa hT hID
    filter_upwards [Hb] with h hh q hq hh0
    exact (mul_pos hb (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hh0))).trans_le (hh q hq)
  filter_upwards [H] with h hh x hx p hp t ht hh0
  let b := extChartAt 𝓘(ℝ,Model n) a x
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x
  let S := L '' activeLogs (n := n) v x
  have hp' : L p ∈ convexHull ℝ S := by
    change L p ∈ convexHull ℝ (L.toLinearMap '' activeLogs v x)
    rw [←L.toLinearMap.image_convexHull]
    exact ⟨p,hp,rfl⟩
  obtain ⟨m,hm0,hmk,z,w,hz,hw,hsum,hmean⟩ := finite_simplex_representation hp'
  let q : EnvelopeData (Model n) (Fin m) := ((b,z),(w,t))
  have hq : q ∈ activeConfiguration v a K T (Fin m) := by
    refine ⟨?_,hw,hsum,ht⟩
    intro i
    obtain ⟨r,hr,hri⟩ := hz i
    refine ⟨(⟨x,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),⟨hr,hx⟩,?_⟩
    have hLr : L r = tangentCoordChange 𝓘(ℝ,Model n) x a x r := by
      dsimp only [L]
      rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
        (show x ∈ (chartAt (Model n) a).source by simpa only [extChartAt_source] using hKa hx)]
      rfl
    change (b,tangentCoordChange 𝓘(ℝ,Model n) x a x r) = (b,z i)
    rw [←hLr,hri]
  have hstrict := hh m (Finset.mem_Icc.mpr ⟨hm0,hmk⟩) q hq hh0
  have hbase : (extChartAt 𝓘(ℝ,Model n) a).symm b = x :=
    (extChartAt 𝓘(ℝ,Model n) a).left_inv (hKa hx)
  have hy : movingNormal a (b,t • ∑ i, w i • z i) = riemannianExp x (t • p) := by
    rw [hmean,←map_smul]
    exact movingNormal_trivialization (hKa hx) (t • p)
  have hx0 : movingNormal a (b,0) = x := by
    rw [movingNormal_zero ((extChartAt 𝓘(ℝ,Model n) a).map_source (hKa hx)),hbase]
  simpa only [q,movingNormalCost,hbase,hy,hx0,b] using hstrict

end WeakMTWTransport

end

end OAI
