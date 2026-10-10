import OAI.NumberTheory.DukePrimeDegree.Geometry.CutFamilyCode
import OAI.NumberTheory.DukePrimeDegree.Geometry.TemperedCutBoundary
import OAI.NumberTheory.DukePrimeDegree.Entropy.VaryingCutItinerary

namespace OAI

/-! # Neighborhoods in countable future atoms from controlled cuts

The actual orbit height selects a finite family of cuts at each time.
Their exponential boundary budget and the radial height budget
make the whole countable future observation locally constant along a
uniformly contracting continuous family.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace DukePrimeDegree

theorem ae_layered_cut_future_neighborhoods
    {Y V : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [TopologicalSpace V] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hTc : Continuous T)
    (H : Y → ℕ) (hH : Measurable H) (hstep : ∀ x, H (T x) ≤ H x+1)
    (f₀ : Y → ℝ) (hf₀ : Continuous f₀) (t : ℕ → ℝ)
    (hlevel : ∀ x m, H x ≤ m ↔ f₀ x ≤ t m)
    (hnull₀ : ∀ m, μ {x | f₀ x=t m}=0)
    {D₀ : ℝ} (hD₀ : 0 ≤ D₀)
    (hbound₀ : ∀ m k, μ (realBoundaryStrip f₀ (t m) ((1/4:ℝ)^k)) ≤
      ENNReal.ofReal (D₀*(1/2:ℝ)^k))
    (N : ℕ → ℕ) (f : ∀ m, Fin (N m) → Y → ℝ)
    (hf : ∀ m i, Continuous (f m i)) (c : ∀ m, Fin (N m) → ℝ)
    (hnull : ∀ m i, μ {x | f m i x=c m i}=0)
    (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hbound : ∀ m i k, μ (realBoundaryStrip (f m i) (c m i) ((1/4:ℝ)^k)) ≤
      ENNReal.ofReal (D m*(1/2:ℝ)^k))
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hsize : ∀ m, (N m:ℝ≥0∞)*ENNReal.ofReal (D m) ≤
      ENNReal.ofReal (K*Real.exp (C*(m:ℝ)))) :
    ∀ᵐ x ∂μ, ∀ (F : V → Y) (v₀ : V), F v₀=x → ContinuousAt F v₀ →
      ∀ U ∈ 𝓝 v₀,
      (∀ k v, v ∈ U → |f₀ (T^[k] (F v))-f₀ (T^[k] x)| ≤ (1/4:ℝ)^k) →
      (∀ k m i v, v ∈ U → |f m i (T^[k] (F v))-f m i (T^[k] x)| ≤ (1/4:ℝ)^k) →
      ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ,
        layeredObservation H (fun m => finiteCutCode (f m) (c m)) (T^[k] (F v)) =
          layeredObservation H (fun m => finiteCutCode (f m) (c m)) (T^[k] x) := by
  have hradial := ae_eventually_avoid_cuts_up_to_height μ hT H hH hstep
    (fun _ => 1) (fun _ _ => f₀) (fun _ _ => hf₀.measurable) (fun m _ => t m)
    (fun _ => D₀) (fun _ => hD₀) (fun m _ k => hbound₀ m k)
    (C := 0) (K := D₀) (by norm_num) hD₀ (by intro m; simp)
  have hcuts := ae_eventually_avoid_cuts_up_to_height μ hT H hH hstep
    N f (fun m i => (hf m i).measurable) c D hD hbound hC hK hsize
  have hn₀ : ∀ᵐ x ∂μ, ∀ m k, f₀ (T^[k] x)≠t m :=
    ae_all_iff.mpr fun m => ae_avoid_cut_boundary_at_all_times μ hT (t m) (hnull₀ m)
  have hn : ∀ᵐ x ∂μ, ∀ m i k, f m i (T^[k] x)≠c m i :=
    ae_all_iff.mpr fun m => ae_all_iff.mpr fun i =>
      ae_avoid_cut_boundary_at_all_times μ hT (c m i) (hnull m i)
  filter_upwards [hradial,hcuts,hn₀,hn] with x hx₀ hx hxn₀ hxn
  intro F v₀ hbase hF U hU hc₀ hc
  have hheight := eventually_radial_height_itinerary_eq hTc H f₀ t hlevel hf₀ hF
    (fun k => (1/4:ℝ)^k)
    (by intro k m; simpa only [hbase] using hxn₀ m k)
    (by simpa only [hbase] using hx₀.mono (fun k hk m hm => hk m hm 0)) U hU
    (by intro k v hv; simpa only [hbase] using hc₀ k v hv)
  have hlabels := eventually_varying_cut_itinerary_eq hTc H N f hf c hF
    (fun k => (1/4:ℝ)^k)
    (by intro k m i; simpa only [hbase] using hxn m i k)
    (by simpa only [hbase] using hx) U hU
    (by intro k m i v hv; simpa only [hbase] using hc k m i v hv)
  have hcodes : ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ,
      finiteCutCode (f (H (T^[k] (F v₀)))) (c (H (T^[k] (F v₀)))) (T^[k] (F v)) =
        finiteCutCode (f (H (T^[k] (F v₀)))) (c (H (T^[k] (F v₀)))) (T^[k] (F v₀)) := by
    filter_upwards [hlabels] with v hv
    intro k
    exact finiteCutCode_eq_of_iff _ _ (hv k)
  simpa only [hbase] using layeredObservation_future_eq H
    (fun m => finiteCutCode (f m) (c m)) T F v₀ hheight hcodes

end DukePrimeDegree

end

end OAI
