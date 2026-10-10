import OAI.Geometry.NodalSets.Waves.UniformChartWaveTransfer

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open Yau.Jets Filter Set
open scoped ContDiff Topology
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem constructed_source_wave_estimates
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → Coord) (hy : Continuous y) (e : T → Coord ≃L[ℝ] Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
    {U : Set Coord} (hU : IsOpen U) (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
    (q : T → Coord) (a bb : T → ℝ) (ha : Continuous a) (hbb : Continuous bb)
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0) (hlen : ∀ t, bb t^2 = a t^2+4)
    (hap : ∀ t, a t • e t (Pi.single 0 1) = metricGradient g S (y t))
    (hbq : ∀ t, bb t • e t (Pi.single 1 1) = q t)
    (hstrict : ∀ t, 0 < sourceHessian g S (y t) (metricGradient g S (y t)) (metricGradient g S (y t)) +
      sourceHessian g S (y t) (q t) (q t)) (m J : ℕ) (K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    ∃ (beta : ContDiffBump (0:Coord)) (phi : T → CPoly) (A : ℕ → T → CPoly)
      (F : T → OpenPartialHomeomorph Coord Coord) (c Cw Cr R : ℝ),
      0 < c ∧ 0 < Cw ∧ 0 < Cr ∧ 0 < R ∧
      MetricWaveJetFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta)
        (fun t ↦ S (y t)) a bb
        (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) m J phi A ∧
      (∀ t, (F t : Coord → Coord) = actualMetricChart g (y t) (e t)) ∧
      ∀ᶠ n : ℕ in atTop, ∀ t,
        let V := chartPushforward (F t) (coordinateWave phi A J (n:ℝ) t)
        ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
        tsupport V ⊆ Metric.closedBall (y t) (R*(n:ℝ)^(-1/3:ℝ)) ∧
        ∀ z : Coord,
          (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val V z‖ ≤
            Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-c*(n:ℝ)*‖z-y t‖^2)) ∧
          DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w V z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*V z) z
              (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z)) := by
  have hB := actualFrameConnection_continuous g hg hpos y hy e he
  obtain ⟨r,hr,d,hd,hcharts⟩ := compact_invariant_charts isCompact_univ g hg hpos w hw y hy e he
    (fun t ↦ actualFrameConnection g (y t) (e t)) hB hU (fun t _ ↦ hyU t) hwpos
  have hcharts' := fun t ↦ hcharts t (mem_univ t)
  choose F hFe hFs hFt hFU hInv hJac hOp using hcharts'
  obtain ⟨beta,phi,A,c,Cr,Cs,hc,hCr,hCs,hjets,hest⟩ := constructed_coordinate_wave_estimates
    g hg hs hpos w hw S hS y hy e he ho hU hyU hwpos q a bb ha hbb ha0 hb0 hlen hap hbq hstrict
    m J K k0 hm hJ
  have hpc : Continuous (fun t ↦ metricChartParameter g (y t) (e t)) := hy.prodMk (he.prodMk hB)
  obtain ⟨c',Cw,Cr',R,hc',hCw,hCr',hR,hsource⟩ := uniform_chart_wave_transfer
    g hg hpos w hw (fun t ↦ metricChartParameter g (y t) (e t)) hpc F hFe r hr hFs hInv hJac
    (fun t z hz ↦ hwpos z (hFU t hz)) S (fun n t ↦ coordinateWave phi A J (n:ℝ) t)
    (fun n t ↦ coordinateWave_smooth phi A J (n:ℝ) t)
    (fun n hn t ↦ coordinateWave_support phi A J (n:ℝ) (by exact_mod_cast hn) t)
    k0 K c Cr Cs hc hCr hCs hest
  exact ⟨beta,phi,A,F,c',Cw,Cr',R,hc',hCw,hCr',hR,hjets,hFe,hsource⟩

end

open Yau.Jets Filter Set
open scoped ContDiff Topology
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem witnessed_source_wave_estimates
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → Coord) (hy : Continuous y) (e : T → Coord ≃L[ℝ] Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
    {U : Set Coord} (hU : IsOpen U) (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
    (q : T → Coord) (a bb : T → ℝ) (ha : Continuous a) (hbb : Continuous bb)
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0) (hlen : ∀ t, bb t^2 = a t^2+4)
    (hap : ∀ t, a t • e t (Pi.single 0 1) = metricGradient g S (y t))
    (hbq : ∀ t, bb t • e t (Pi.single 1 1) = q t)
    (hstrict : ∀ t, 0 < sourceHessian g S (y t) (metricGradient g S (y t)) (metricGradient g S (y t)) +
      sourceHessian g S (y t) (q t) (q t)) (m J : ℕ) (K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    ∃ (beta : ContDiffBump (0:Coord)) (phi : T → CPoly) (A : ℕ → T → CPoly)
      (F : T → OpenPartialHomeomorph Coord Coord) (c Cw Cr R r d : ℝ),
      0 < c ∧ 0 < Cw ∧ 0 < Cr ∧ 0 < R ∧ 0 < r ∧ 0 < d ∧
      MetricWaveJetFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta)
        (fun t ↦ S (y t)) a bb
        (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) m J phi A ∧
      (∀ t, (F t : Coord → Coord) = actualMetricChart g (y t) (e t)) ∧
      (∀ t, (F t).source = Metric.ball 0 r ∧ Metric.closedBall (y t) d ⊆ (F t).target ∧
        ContDiffOn ℝ ∞ (F t).symm (F t).target) ∧
      ∀ᶠ n : ℕ in atTop, ∀ t,
        let V := chartPushforward (F t) (coordinateWave phi A J (n:ℝ) t)
        ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
        tsupport V ⊆ Metric.closedBall (y t) (R*(n:ℝ)^(-1/3:ℝ)) ∧
        ∀ z : Coord,
          (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val V z‖ ≤
            Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-c*(n:ℝ)*‖z-y t‖^2)) ∧
          DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w V z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*V z) z
              (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z)) := by
  have hB := actualFrameConnection_continuous g hg hpos y hy e he
  obtain ⟨r,hr,d,hd,hcharts⟩ := compact_invariant_charts isCompact_univ g hg hpos w hw y hy e he
    (fun t ↦ actualFrameConnection g (y t) (e t)) hB hU (fun t _ ↦ hyU t) hwpos
  have hcharts' := fun t ↦ hcharts t (mem_univ t)
  choose F hFe hFs hFt hFU hInv hJac hOp using hcharts'
  obtain ⟨beta,phi,A,c,Cr,Cs,hc,hCr,hCs,hjets,hest⟩ := constructed_coordinate_wave_estimates
    g hg hs hpos w hw S hS y hy e he ho hU hyU hwpos q a bb ha hbb ha0 hb0 hlen hap hbq hstrict
    m J K k0 hm hJ
  have hpc : Continuous (fun t ↦ metricChartParameter g (y t) (e t)) := hy.prodMk (he.prodMk hB)
  obtain ⟨c',Cw,Cr',R,hc',hCw,hCr',hR,hsource⟩ := uniform_chart_wave_transfer
    g hg hpos w hw (fun t ↦ metricChartParameter g (y t) (e t)) hpc F hFe r hr hFs hInv hJac
    (fun t z hz ↦ hwpos z (hFU t hz)) S (fun n t ↦ coordinateWave phi A J (n:ℝ) t)
    (fun n t ↦ coordinateWave_smooth phi A J (n:ℝ) t)
    (fun n hn t ↦ coordinateWave_support phi A J (n:ℝ) (by exact_mod_cast hn) t)
    k0 K c Cr Cs hc hCr hCs hest
  exact ⟨beta,phi,A,F,c',Cw,Cr',R,r,d,hc',hCw,hCr',hR,hr,hd,hjets,hFe,
    (fun t ↦ ⟨hFs t,hFt t,hInv t⟩),hsource⟩

end Yau.Geometry

end

end OAI
