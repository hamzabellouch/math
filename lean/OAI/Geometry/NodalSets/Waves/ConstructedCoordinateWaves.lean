import OAI.Geometry.NodalSets.Coefficients.CoefficientCutoffRemoval

namespace OAI

namespace Yau.Geometry
open Filter Set MvPolynomial
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

def coordinateWave (phi : T → CPoly) (A : ℕ → T → CPoly) (J : ℕ) (N : ℝ)
    (t : T) (x : Coord) : ℂ :=
  Yau.Waves.scaledCutoff N (0:Coord) x •
    (finiteAmplitude (fun j ↦ A j t) J N x * waveExp (reval (phi t)) N x)

omit [TopologicalSpace T] [CompactSpace T] in
lemma coordinateWave_smooth (phi : T → CPoly) (A : ℕ → T → CPoly) (J : ℕ) (N : ℝ) (t : T) :
    ContDiff ℝ ∞ (coordinateWave phi A J N t) :=
  (Yau.Waves.scaledCutoff_contDiff N (0:Coord)).smul
    ((finiteAmplitude_contDiff _ _ _).mul (waveExp_contDiff (reval_contDiff _) N))

omit [TopologicalSpace T] [CompactSpace T] in
lemma coordinateWave_support (phi : T → CPoly) (A : ℕ → T → CPoly) (J : ℕ) (N : ℝ)
    (hN : 0 < N) (t : T) :
    tsupport (coordinateWave phi A J N t) ⊆ Metric.closedBall 0 (2*N^(-1/3:ℝ)) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hb : Yau.Waves.scaledCutoff N (0:Coord) x ≠ 0 := by
    intro hz
    exact hx (by simp [coordinateWave,hz])
  have hh : x ∈ Function.support (Yau.Waves.scaledCutoff N (0:Coord)) := hb
  rw [Yau.Waves.scaledCutoff_support hN] at hh
  exact Metric.ball_subset_closedBall hh

theorem constructed_coordinate_wave_estimates
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
      (c Cr : ℝ) (Cs : Fin (k0+1) → ℝ),
      0 < c ∧ 0 < Cr ∧ (∀ k, 0 < Cs k) ∧
      MetricWaveJetFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta)
        (fun t ↦ S (y t)) a bb
        (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) m J phi A ∧
      ∀ᶠ n : ℕ in atTop, ∀ t, ∀ x : Coord,
        (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (coordinateWave phi A J (n:ℝ) t) x‖ ≤
          Cs k*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S (actualMetricChart g (y t) (e t) x)-c*(n:ℝ)*‖x‖^2)) ∧
        DerivativeBound k0 (fun z ↦ smoothSecondOrder (fun i j ↦ complexPrincipal g i j (metricChartParameter g (y t) (e t)))
          (fun j ↦ complexDrift g w j (metricChartParameter g (y t) (e t))) (coordinateWave phi A J (n:ℝ) t) z +
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*coordinateWave phi A J (n:ℝ) t z) x
          (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S (actualMetricChart g (y t) (e t) x))) := by
  obtain ⟨beta,phi,A,hG,hjets,c,hc,hgap⟩ := compact_actual_metric_wave_jets
    g hg hs hpos w hw S hS y hy e he ho hU hyU hwpos q a bb ha hbb ha0 hb0 hlen hap hbq hstrict
    m J (by omega)
  obtain ⟨Cr,hCr,hres⟩ := hjets.global_residual hG
    (fun t x ↦ S (actualMetricChart g (y t) (e t) x)) c hc hgap K k0 hm hJ
  have hsize (k : Fin (k0+1)) := uniform_cutoff_wave_size isCompact_univ phi A
    hjets.phase_continuous hjets.amplitude_continuous J k.val
    (fun t x ↦ S (actualMetricChart g (y t) (e t) x)) c hc
    (hgap.mono (fun _ h t _ ↦ h t))
  choose Cs hCs hsize using hsize
  refine ⟨beta,phi,A,c,Cr,Cs,hc,hCr,hCs,hjets,?_⟩
  have hreal : ∀ᶠ N : ℝ in atTop, ∀ t, ∀ x : Coord,
      (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (coordinateWave phi A J N t) x‖ ≤
        Cs k*N^k.val*Real.exp (N*S (actualMetricChart g (y t) (e t) x)-c*N*‖x‖^2)) ∧
      DerivativeBound k0 (fun z ↦ smoothSecondOrder (fun i j ↦ complexPrincipal g i j (metricChartParameter g (y t) (e t)))
        (fun j ↦ complexDrift g w j (metricChartParameter g (y t) (e t))) (coordinateWave phi A J N t) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ))*coordinateWave phi A J N t z) x
        (Cr*N^(-(K:ℝ))*Real.exp (N*S (actualMetricChart g (y t) (e t) x))) := by
    filter_upwards [hres,Filter.eventually_all.mpr hsize,coefficient_cutoff_operator_eq beta]
      with N hrN hsN heq
    intro t x
    refine ⟨fun k ↦ hsN k t (mem_univ t) x,?_⟩
    have he := heq
      (fun i j ↦ complexPrincipal g i j (metricChartParameter g (y t) (e t)))
      (fun j ↦ complexDrift g w j (metricChartParameter g (y t) (e t)))
      (fun z ↦ finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z)
    have hbound := hrN t x
    change DerivativeBound k0 (fun z ↦
      smoothSecondOrder (fun i j x ↦ beta x • complexPrincipal g i j (metricChartParameter g (y t) (e t)) x)
        (fun j x ↦ beta x • complexDrift g w j (metricChartParameter g (y t) (e t)) x)
        (coordinateWave phi A J N t) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ))*coordinateWave phi A J N t z) x _ at hbound
    change smoothSecondOrder _ _ (coordinateWave phi A J N t) = _ at he
    rw [he] at hbound
    exact hbound
  simpa only [Complex.ofReal_natCast] using eventually_nat_frequency hreal

end
end Yau.Geometry

end OAI
