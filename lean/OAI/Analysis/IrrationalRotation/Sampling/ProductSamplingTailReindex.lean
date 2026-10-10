import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTrimming

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductModel

theorem HasUniformL2Marginals.comp {η : ℕ → Measure EndpointPair}
    (h : HasUniformL2Marginals η) (r : ℕ → ℕ) :
    HasUniformL2Marginals (fun l => η (r l)) := by
  obtain ⟨H, hH, h⟩ := h
  exact ⟨H, hH, fun l => h (r l)⟩

theorem WeaklyConverges.comp_tendsto {η : ℕ → Measure EndpointPair}
    {ν : Measure EndpointPair} (h : WeaklyConverges η ν)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) :
    WeaklyConverges (fun l => η (r l)) ν := by
  intro φ
  exact (h φ).comp hr

namespace TailTrimming

theorem orderedOrbitSampling_of_eventually_prefix_samples
    (θ : ℕ → ℝ) (I : Finset ℕ) (hθ : ∀ i, 0 ≤ θ i)
    (D N : ℕ → Finset ℕ) (M : ℕ → ℕ)
    (w : ∀ l, ℕ → (D l → Circle) → ℝ≥0∞)
    (hw : ∀ᶠ l in atTop, ∀ n ∈ N l, Measurable (w l n))
    (hN : ∀ᶠ l in atTop, ∀ n ∈ N l, 0 < n)
    (hM : ∀ᶠ l in atTop, ∀ n ∈ N l, n ≤ M l)
    (hprefix : ∀ᶠ l in atTop, ∀ n ∈ N l,
      ∀ᵐ x ∂baseMeasure.withDensity (fun x : Base => w l n (fun i : D l => x i)),
        ∀ i ∈ D l, circleRepresentative (x i) ≤
          circleRepresentative (rotationIterate θ (n : ℤ) x i))
    (hL2 : HasUniformL2Marginals
      (fun l => orbitAverageMeasure θ (N l) (fun n x => w l n (fun i : D l => x i))))
    (hweak : WeaklyConverges
      (fun l => orbitAverageMeasure θ (N l) (fun n x => w l n (fun i : D l => x i)))
      (triangularLaw I))
    (htail : Tendsto (fun l => ENNReal.ofReal (M l : ℝ) *
      ∑' i : {i : ℕ // i ∉ D l}, ENNReal.ofReal (θ i)) atTop (𝓝 0)) :
    OrderedOrbitSampling θ I := by
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hw.and (hN.and (hM.and hprefix)))
  have hshift : Tendsto (fun l : ℕ => l + J) atTop atTop :=
    tendsto_atTop_mono (fun l => Nat.le_add_right l J) tendsto_id
  have hstage (l : ℕ) := hJ (l + J) (Nat.le_add_left J l)
  exact orderedOrbitSampling_of_prefix_samples θ I hθ
    (fun l => D (l + J)) (fun l => N (l + J)) (fun l => M (l + J))
    (fun l => w (l + J)) (fun l => (hstage l).1)
    (fun l => (hstage l).2.1) (fun l => (hstage l).2.2.1)
    (fun l => (hstage l).2.2.2) (hL2.comp (fun l => l + J))
    (hweak.comp_tendsto hshift) (htail.comp hshift)

end TailTrimming
end Invariant233.ProductModel

end

end OAI
