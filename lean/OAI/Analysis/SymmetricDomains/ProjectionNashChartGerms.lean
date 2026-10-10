import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicAnalyticLocalInverse

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology

theorem inverse_germ_boundary_transfer {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U V : Set Y) (hUV : U ⊆ V) (hV : IsClosed V)
    (F : X → Y) (G : Y → X) (hG : Continuous G) (p : Y)
    (hFG : ∀ᶠ y in 𝓝[V] p, F (G y) = y)
    (T : Set X) (hT : IsOpen T) (hpT : G p ∈ T) :
    ∃ W : Set Y, IsOpen W ∧ p ∈ W ∧
      ∀ y ∈ (closure U \ U) ∩ W,
        G y ∈ (closure (T ∩ F ⁻¹' U) \ (T ∩ F ⁻¹' U)) ∧
        G y ∈ T ∧ F (G y) = y := by
  have hfg := eventually_nhdsWithin_iff.mp hFG
  have hgt : ∀ᶠ y in 𝓝 p, G y ∈ T :=
    hG.continuousAt.preimage_mem_nhds (hT.mem_nhds hpT)
  obtain ⟨W,hW,hWo,hpW⟩ := mem_nhds_iff.mp (hfg.and hgt)
  refine ⟨W,hWo,hpW,?_⟩
  intro y hy
  have hyV : y ∈ V := closure_minimal hUV hV hy.1.1
  have hgy : F (G y) = y := (hW hy.2).1 hyV
  have hym : y ∈ closure (W ∩ U) := hWo.inter_closure ⟨hy.2,hy.1.1⟩
  have hmap : MapsTo G (W ∩ U) (T ∩ F ⁻¹' U) := by
    intro z hz
    exact ⟨(hW hz.1).2,by change F (G z) ∈ U; rw [(hW hz.1).1 (hUV hz.2)]; exact hz.2⟩
  refine ⟨⟨hG.continuousAt.continuousWithinAt.mem_closure hym hmap,?_⟩,
    (hW hy.2).2,hgy⟩
  intro hz
  apply hy.1.2
  simpa only [mem_preimage,hgy] using hz.2

theorem semialgebraic_nash_chart_preimage {m N : ℕ}
    {U : Set (Affine N)} (hU : IsSemialgebraic U)
    {B : Set (Fin (m+m) → ℝ)} (H : Affine m → Affine N)
    (hH : SemialgebraicOn B
      (fun x => complexRealEquiv N (H ((complexRealEquiv m).symm x)))) :
    PolynomialSignSet id (B ∩ (fun x => H ((complexRealEquiv m).symm x)) ⁻¹' U) := by
  convert hH.preimage (isSemialgebraic_real_image hU) using 1
  ext x
  simp only [mem_inter_iff,mem_preimage,mem_image]
  constructor
  · rintro ⟨hx,hy⟩
    exact ⟨hx,_,hy,rfl⟩
  · rintro ⟨hx,y,hy,he⟩
    exact ⟨hx,(complexRealEquiv N).injective he ▸ hy⟩
end

open Set Filter Topology Metric
open scoped Classical

structure ProjectionNashChart {N : ℕ} (V : Set (Affine N)) (p : Affine N) (m : ℕ) where
  projection : Affine N →L[ℂ] Affine m
  inverse : Affine m → Affine N
  radius : ℝ
  radius_pos : 0 < radius
  inverse_zero : inverse 0 = p
  inverse_analytic : AnalyticOnNhd ℂ inverse {z | ‖complexRealEquiv m z‖ < radius}
  inverse_semialgebraic : SemialgebraicOn {x : Fin (m+m) → ℝ | ‖x‖ < radius}
    (fun x => complexRealEquiv N (inverse ((complexRealEquiv m).symm x)))
  left_inverse : ∀ z, ‖complexRealEquiv m z‖ < radius → projection (inverse z-p) = z
  right_inverse : ∀ᶠ y in 𝓝[V] p, inverse (projection (y-p)) = y
  inverse_mem : ∀ z, ‖complexRealEquiv m z‖ < radius → inverse z ∈ V

theorem projection_nash_chart_of_germs {m N : ℕ} (V : Set (Affine N))
    (hV : IsSemialgebraic V) (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (F 0))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (F 0), F (G y) = y)
    (hFV : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V) :
    Nonempty (ProjectionNashChart V (F 0) m) := by
  obtain ⟨π,H,h0,hH,hπH,hHπ,hHV,r,hr,hHs⟩ :=
    semialgebraic_projection_chart_germ V hV F G hF hG hGF hFG hFV
  have ht : Tendsto (complexRealEquiv m).symm (𝓝 (0 : Fin (m+m) → ℝ)) (𝓝 0) := by
    simpa only [map_zero] using (complexRealEquiv m).symm.continuous.tendsto 0
  have hn := ht (hH.eventually_analyticAt.and (hπH.and hHV))
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp hn
  let ρ := min r R
  have hρ : 0 < ρ := lt_min hr hR
  have hρsub {z : Affine m} (hz : ‖complexRealEquiv m z‖ < ρ) :
      AnalyticAt ℂ H z ∧ π (H z-F 0) = z ∧ H z ∈ V := by
    have hh := hsub (show complexRealEquiv m z ∈ ball 0 R from by
      simpa only [mem_ball,dist_zero_right] using lt_of_lt_of_le hz (min_le_right r R))
    simpa only [mem_preimage,mem_ofPred_eq,ContinuousLinearEquiv.symm_apply_apply] using hh
  refine ⟨⟨π,H,ρ,hρ,h0,(fun z hz => (hρsub hz).1),?_,
    (fun z hz => (hρsub hz).2.1),hHπ,(fun z hz => (hρsub hz).2.2)⟩⟩
  exact hHs.mono (by simpa only [sub_zero] using polynomialSignSet_real_ball (0 : Fin (m+m) → ℝ) ρ)
    (fun _ hz => lt_of_lt_of_le hz (min_le_left r R))
end Release061

end

end OAI
