import Mathlib
import OAI.Geometry.NearbyLagrangian.AnalyticObstruction
import OAI.Geometry.NearbyLagrangian.QuadraticStability
import OAI.Geometry.NearbyLagrangian.SmoothTubeApproximation

namespace OAI

/-! Class persistence and the conditional reduction to the two topological hypotheses. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes
open Transport CotangentGeometry EmbeddedRealization Cutoff Scales RegularHomogeneous Set
open scoped Manifold ContDiff Topology

theorem localized_analytic_obstruction {m : ℕ} (hm : 0 < m)
    (a : C(Sphere 9,Tube m m)) :
    ∃ b : C(Sphere 9,Tube m m), a.Homotopic b ∧
      ∃ K Λ T : ℝ, 0 < K ∧ 0 < Λ ∧ 1 < T ∧
        IsClosedExactLagrangian (realization (realizationFamily hm b)
          (exponentialScale (SphereDirection.height heightAxis) K Λ) T) ∧
        (IsHamiltonianImage (realization (realizationFamily hm b)
          (exponentialScale (SphereDirection.height heightAxis) K Λ) T) →
          HasRestoredEndpoint b (10+((2*m-1)+1))) := by
  obtain ⟨b,hab,hbs,hbj,_,hfix⟩ := smooth_localized_tube_C1 (by omega) a capEquator
  have hcap : ∀ x : Sphere 9, (31:ℝ)/32 < |SphereDirection.height heightAxis x| →
      Function.Injective (gradient (b x).val) := by
    intro x hx
    rw [hfix x (SphereCollapse.polar_cap_in_plateau capEquator x
      heightAxis_norm heightAxis_inner_capEquator hx)]
    exact standardForm_gradient_injective m m
  exact ⟨b,hab,source_analytic_obstruction hm b hbs hbj hcap⟩

theorem HasRestoredEndpoint.class_persistence {m d : ℕ} (hm : 20 ≤ m)
    {a : C(Sphere 9,Tube m m)} (ha : StablyNonNull a) (hn : StableNegativeTrivial a)
    (he : HasRestoredEndpoint a d) :
    ∃ p : ℕ, 20 ≤ p ∧ ∃ δ : C(Sphere 9,Tube p p),
      StablyNonNull δ ∧ StableNegativeTrivial δ ∧
      ∃ (H : Sphere 9 × Euclidean (p+p) → ℝ) (σ : Sphere 9 → Euclidean (p+p)) (R : ℝ),
        0 < R ∧
        (∀ q : Sphere 9 × Euclidean (p+p), q.2 ≠ 0 →
          ContMDiffAt ((𝓡 9).prod 𝓘(ℝ,Euclidean (p+p))) 𝓘(ℝ,ℝ) ∞
            (fun q => (δ q.1).val q.2) q) ∧
        ContMDiff ((𝓡 9).prod 𝓘(ℝ,Euclidean (p+p))) 𝓘(ℝ,ℝ) ∞ H ∧
        (∀ q, R ≤ ‖q.2‖ → H q = (δ q.1).val q.2) ∧
        ContMDiff (𝓡 9) 𝓘(ℝ,Euclidean (p+p)) ∞ σ ∧
        (∀ b w, fderiv ℝ (fun w => H (b,w)) w = 0 ↔ w = σ b) ∧
        (∀ b, Function.Bijective (fderiv ℝ (fderiv ℝ (fun w => H (b,w))) (σ b))) := by
  obtain ⟨t,R,δ,H,σ,hR,hH,hδ,hHs,ht,hσ,hu,hnd⟩ := he
  have hmp : 0 < m := by omega
  have hp : 0 < transportIndex m d t := lt_of_lt_of_le hmp (le_transportIndex m d t)
  have hnon : StablyNonNull δ := (ha.addBalancedFor d t).of_homotopic hH
  have hneg : StableNegativeTrivial δ :=
    (hn.addBalancedFor (V:=Euclidean 9) hmp d t).of_homotopic (V:=Euclidean 9) hp hH
  exact ⟨transportIndex m d t,hm.trans (le_transportIndex m d t),δ,hnon,hneg,
    H,σ,2*R,by linarith,hδ,hHs,ht,hσ,hu,hnd⟩

end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Tubes
open Set
open scoped Manifold ContDiff Topology

def OneCriticalTubeNullityGoal : Prop :=
  ∀ p : ℕ, 20 ≤ p →
  ∀ a : C(Metric.sphere (0 : Euclidean 10) 1, Tube p p),
  ∀ F : Metric.sphere (0 : Euclidean 10) 1 × Euclidean (p+p) → ℝ,
    (∀ q : Metric.sphere (0 : Euclidean 10) 1 × Euclidean (p+p), q.2 ≠ 0 →
      ContMDiffAt ((𝓡 9).prod 𝓘(ℝ,Euclidean (p+p))) 𝓘(ℝ,ℝ) ∞
        (fun q => (a q.1).val q.2) q) →
    ContMDiff ((𝓡 9).prod 𝓘(ℝ,Euclidean (p+p))) 𝓘(ℝ,ℝ) ∞ F →
    (∃ R : ℝ, 0 < R ∧ ∀ b w, R ≤ ‖w‖ → F (b,w) = (a b).val w) →
    (∃ s : Metric.sphere (0 : Euclidean 10) 1 → Euclidean (p+p),
      ContMDiff (𝓡 9) 𝓘(ℝ,Euclidean (p+p)) ∞ s ∧
      (∀ b w, fderiv ℝ (fun z => F (b,z)) w = 0 ↔ w = s b) ∧
      ∀ b, Function.Bijective (fderiv ℝ (fderiv ℝ (fun z => F (b,z))) (s b))) →
    StableNegativeTrivial a →
    ∃ r : ℕ, ((stabilizeFor p r).comp a).Nullhomotopic

end NearbyLagrangian.Tubes

namespace NearbyLagrangian
open Tubes EmbeddedRealization Scales

theorem main_reduction (hkernel : Tubes.KernelFamilyGoal)
    (hone : Tubes.OneCriticalTubeNullityGoal) : MainStatement := by
  obtain ⟨m,hm,a,ha,hn⟩ := hkernel
  obtain ⟨b,hab,K,Λ,T,hK,hΛ,hT,hL,htransport⟩ :=
    Tubes.localized_analytic_obstruction (by omega : 0 < m) a
  refine ⟨m,hm,EmbeddedRealization.realization (Tubes.realizationFamily (by omega) b)
    (Scales.exponentialScale (SphereDirection.height Tubes.heightAxis) K Λ) T,hL,?_⟩
  intro hi
  have hb : Tubes.StablyNonNull b := ha.of_homotopic hab
  have hnb : Tubes.StableNegativeTrivial b :=
    hn.of_homotopic (V:=Euclidean 9) (by omega) hab
  obtain ⟨p,hp,δ,hδ,hnδ,H,σ,R,hR,hδs,hHs,ht,hσ,hu,hnd⟩ :=
    (htransport hi).class_persistence hm hb hnb
  obtain ⟨r,hr⟩ := hone p hp δ H hδs hHs
    ⟨R,hR,fun b w hw => ht (b,w) hw⟩ ⟨σ,hσ,hu,hnd⟩ hnδ
  exact hδ r hr

end NearbyLagrangian

end

end OAI
