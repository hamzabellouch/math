import OAI.MeasureTheory.Falconer.Graphs.GraphAmplitudeDerivatives
import OAI.MeasureTheory.Falconer.Fourier.GraphActualFrequencySupport

namespace OAI

namespace PlanarFalconer
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology

def graphAmplitudeCompact : Set (Plane × ℝ) :=
  (closedBall 0 8 ×ˢ Icc (-4) 4) ∩ {p | 1/8 ≤ ‖p.1‖}

theorem graphAmplitudeCompact_isCompact : IsCompact graphAmplitudeCompact :=
  ((isCompact_closedBall (0:Plane) 8).prod isCompact_Icc).inter_right
    (isClosed_le continuous_const continuous_fst.norm)

theorem graphAmplitudePullback_norm_transport (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    (Ψ : ℝ → ℝ) (R : ℝ) (p : Plane × ℝ) :
    ‖graphAmplitudePullback b x distance plus axis δ j k Ψ p‖ =
      ‖graphTransport (graphFourKernel b (graphSourceWeight distance plus axis (angularBinCount δ) j k) x)
        Ψ R (graphSourceChartAxis distance plus) (p.2,p.1)‖ := by
  simp only [graphAmplitudePullback,graphShellJacobian,graphTransport,graphFourKernel,
    norm_smul,norm_mul,sourcePlaneWave_norm,one_mul,mul_one,Complex.norm_real]
  ring

theorem graphAmplitudePullback_tsupport (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    tsupport (graphAmplitudePullback b x distance plus axis δ j k Ψ) ⊆ graphAmplitudeCompact := by
  apply closure_minimal _ graphAmplitudeCompact_isCompact.isClosed
  intro p hp
  have hn : graphTransport
      (graphFourKernel b (graphSourceWeight distance plus axis (angularBinCount δ) j k) x)
      Ψ 1 (graphSourceChartAxis distance plus) (p.2,p.1) ≠ 0 := by
    intro he
    apply hp
    apply norm_eq_zero.mp
    rw [graphAmplitudePullback_norm_transport b x distance plus axis δ j k Ψ 1 p,he,norm_zero]
  have hb := graphActualTransport_frequency_support b x distance plus axis (angularBinCount δ) j k hsupp 1 (p.2,p.1) hn
  refine ⟨⟨?_,abs_le.mp hb.2.2⟩,hb.1⟩
  simpa only [mem_closedBall,dist_zero_right] using hb.2.1

theorem graphAmplitudePullback_hasCompactSupport (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    HasCompactSupport (graphAmplitudePullback b x distance plus axis δ j k Ψ) :=
  graphAmplitudeCompact_isCompact.of_isClosed_subset isClosed_closure
    (graphAmplitudePullback_tsupport b x distance plus axis δ j k hsupp)

theorem GraphDerivativeBound.global_smooth {n : ℕ} {f : (Plane × ℝ) → ℂ} {C D : ℝ}
    (hf : GraphDerivativeBound n f C D) (hs : tsupport f ⊆ graphAmplitudeCompact) :
    ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 ≠ 0
  · exact (hf.smooth p hp).contDiffAt (graphSmoothDomain_isOpen.mem_nhds hp)
  · have hn : p ∉ tsupport f := by
      intro hmem
      have hlo : (1:ℝ)/8 ≤ ‖p.1‖ := (hs hmem).2
      rw [not_ne_iff.mp hp,norm_zero] at hlo
      norm_num at hlo
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with q hq
    exact image_eq_zero_of_notMem_tsupport hq

theorem GraphDerivativeBound.global_bound {n : ℕ} {f : (Plane × ℝ) → ℂ} {C D : ℝ}
    (hf : GraphDerivativeBound n f C D) (hs : tsupport f ⊆ graphAmplitudeCompact)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (j : ℕ) (hj : j ≤ n) (p : Plane × ℝ) :
    ‖iteratedFDeriv ℝ j f p‖ ≤ C*D^j := by
  by_cases hp : p ∈ graphAmplitudeCompact
  · apply hf.bound j hj p.1 p.2 _ (abs_le.mpr hp.1.2) hp.2
    simpa only [mem_closedBall,dist_zero_right] using hp.1.1
  · have hz : iteratedFDeriv ℝ j f p = 0 := by
      apply Function.notMem_support.mp
      intro hmem
      exact hp (hs (support_iteratedFDeriv_subset j hmem))
    rw [hz,norm_zero]
    exact mul_nonneg hC (pow_nonneg hD j)

end PlanarFalconer

end OAI
