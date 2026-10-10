import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.MinimizingSegments
import OAI.Geometry.WeakMTW.Variations.BrokenActionCalculus
import OAI.Geometry.WeakMTW.Coordinates.FanCoordinates
import OAI.Geometry.WeakMTW.Coordinates.CostEndpointAction

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace DiscreteVariational
 theorem three_action_bound {τ ε N₀ N d e : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    (hN₀ : 0 ≤ N₀) (hN : 0 ≤ N) (hd : 0 ≤ d) (he : 0 ≤ e)
    (htri : (τ+ε+ε)*N₀ ≤ τ*N+d+e) :
    (τ+ε+ε)/2*N₀^2 ≤ τ/2*N^2 + (d^2/2)/ε + (e^2/2)/ε := by
  have hsum : 0 < τ+ε+ε := by positivity
  have hsq : ((τ+ε+ε)*N₀)^2 ≤ (τ*N+d+e)^2 :=
    (sq_le_sq₀ (mul_nonneg hsum.le hN₀)
      (add_nonneg (add_nonneg (mul_nonneg hτ.le hN) hd) he)).mpr htri
  have hh := (div_le_div_of_nonneg_right hsq hsum.le).trans
    (weighted_three_sq (τ*N) d e τ ε ε hτ hε hε)
  have h₁ : ((τ+ε+ε)*N₀)^2/(τ+ε+ε) = (τ+ε+ε)*N₀^2 := by
    field_simp
  have h₂ : (τ*N)^2/τ = τ*N^2 := by field_simp
  rw [h₁,h₂] at hh
  convert (div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 2)) using 1 <;> (first | rfl | ring)
end DiscreteVariational

namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem chartCost_fan (x : M) (P : ℝ → TangentBundle (model n) M)
    {t s u r : ℝ} (ht : (t,s) ∈ fanDomain x P) (hu : (u,r) ∈ fanDomain x P) :
    chartCost x ((fanCoordinates x P (t,s)).1,(fanCoordinates x P (u,r)).1) =
      cost (geodesic (P s) t) (geodesic (P r) u) := by
  change cost ((chartAt (Model n) x).symm (chartAt (Model n) x (geodesic (P s) t)))
      ((chartAt (Model n) x).symm (chartAt (Model n) x (geodesic (P r) u))) = _
  have hts : geodesic (P s) t ∈ (chartAt (Model n) x).source := (stateChart_source x _).mp ht
  have hus : geodesic (P r) u ∈ (chartAt (Model n) x).source := (stateChart_source x _).mp hu
  rw [(chartAt (Model n) x).left_inv hts,(chartAt (Model n) x).left_inv hus]

 theorem brokenAction_minimum (x : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P)
    (b : M) (hbase : ∀ s, (P s).1 = b) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    (hm : dist b (geodesic (P 0) (1+ε)) = (1+ε)*‖(P 0).2‖)
    (ha : (1-ε,0) ∈ fanDomain x P) (hc : (1,0) ∈ fanDomain x P)
    (hz : (1+ε,0) ∈ fanDomain x P) :
    IsLocalMin (brokenAction (chartCost x) (fun s => ‖(P s).2‖^2)
      (fun s => (fanCoordinates x P (1-ε,s)).1) (1-ε) ε
      (fanCoordinates x P (1+ε,0)).1) (0,(fanCoordinates x P (1,0)).1) := by
  let C := chartAt (Model n) x
  let f := brokenAction (chartCost x) (fun s => ‖(P s).2‖^2)
      (fun s => (fanCoordinates x P (1-ε,s)).1) (1-ε) ε (fanCoordinates x P (1+ε,0)).1
  have hεn : ε ≠ 0 := hε.ne'
  have ha' : 0 ≤ 1-ε := sub_nonneg.mpr hε₁.le
  have hd₁ := minimizing_segment_dist (P 0) (L := 1+ε) (a := 1-ε) (b := 1)
    (by simpa only [hbase] using hm) ha' (by linarith) (by linarith)
  have hd₂ := minimizing_segment_dist (P 0) (L := 1+ε) (a := 1) (b := 1+ε)
    (by simpa only [hbase] using hm) (by norm_num) (by linarith) le_rfl
  have hf₀ : f (0,(fanCoordinates x P (1,0)).1) = (1+ε)/2*‖(P 0).2‖^2 := by
    dsimp only [f,brokenAction]
    rw [chartCost_fan x P ha hc,chartCost_fan x P hc hz]
    unfold cost
    rw [hd₁,hd₂]
    field_simp
    ring
  have hCa : ∀ᶠ q : ℝ × Model n in 𝓝 (0,(fanCoordinates x P (1,0)).1),
      (1-ε,q.1) ∈ fanDomain x P :=
    (continuousAt_const.prodMk continuousAt_fst).preimage_mem_nhds ((fanDomain_open x hP).mem_nhds ha)
  change ∀ᶠ q in 𝓝 (0,(fanCoordinates x P (1,0)).1), f (0,(fanCoordinates x P (1,0)).1) ≤ f q
  filter_upwards [hCa] with q hq
  rw [hf₀]
  have hd := geodesic_dist_le (P q.1) 0 (1-ε)
  rw [geodesic_zero,sub_zero,abs_of_nonneg ha'] at hd
  have hd' : dist b (geodesic (P q.1) (1-ε)) ≤ ‖(P q.1).2‖*(1-ε) := by
    calc
      _ = dist (P q.1).1 (geodesic (P q.1) (1-ε)) :=
        congrArg (fun z => dist z (geodesic (P q.1) (1-ε))) (hbase q.1).symm
      _ ≤ _ := hd
  have ht := dist_triangle4 b (geodesic (P q.1) (1-ε)) (C.symm q.2) (geodesic (P 0) (1+ε))
  rw [hm] at ht
  have htri : ((1-ε)+ε+ε)*‖(P 0).2‖ ≤ (1-ε)*‖(P q.1).2‖ +
      dist (geodesic (P q.1) (1-ε)) (C.symm q.2) + dist (C.symm q.2) (geodesic (P 0) (1+ε)) := by
    calc
      _ = (1+ε)*‖(P 0).2‖ := by congr 1; ring
      _ ≤ _ := ht.trans (by
        gcongr
        simpa only [mul_comm] using hd')
  have hb := three_action_bound (sub_pos.mpr hε₁) hε (norm_nonneg _) (norm_nonneg _)
    (dist_nonneg (x := geodesic (P q.1) (1-ε)) (y := C.symm q.2))
    (dist_nonneg (x := C.symm q.2) (y := geodesic (P 0) (1+ε))) htri
  dsimp only [f,brokenAction,chartCost,fanCoordinates,geodesicFan] at ⊢
  change _ ≤ (1-ε)/2*‖(P q.1).2‖^2 +
    cost (C.symm (C (geodesic (P q.1) (1-ε)))) (C.symm q.2)/ε +
    cost (C.symm q.2) (C.symm (C (geodesic (P 0) (1+ε))))/ε
  have hqs : geodesic (P q.1) (1-ε) ∈ C.source := (stateChart_source x _).mp hq
  have hzs : geodesic (P 0) (1+ε) ∈ C.source := (stateChart_source x _).mp hz
  rw [C.left_inv hqs,C.left_inv hzs]
  unfold cost
  convert hb using 1
  ring

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
