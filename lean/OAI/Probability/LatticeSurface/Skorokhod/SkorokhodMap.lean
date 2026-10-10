import Mathlib
import OAI.Probability.LatticeSurface.Brownian.BrownianFacet

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set Filter ConvexSkorokhod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem measurable_reflected_path_map (B : Body E) (x c : E) (r R : ℝ)
    (hx : x∈B.carrier) (hr : 0<r) (hball : Metric.closedBall c r⊆B.carrier)
    (hR : ∀z∈B.carrier,‖z-c‖≤R) :
    ∃Φ : VectorPath E → VectorPath E,Continuous Φ ∧ Measurable Φ ∧
      ∀f : VectorPath E,∃u k : ℝ → E,∃ν : VectorMeasure unitInterval E,
        (∀t : Set.Icc (0:ℝ) 1,Φ f t=u t) ∧
        ContinuousOn u (Icc 0 1) ∧ ContinuousOn k (Icc 0 1) ∧
        u 0=x ∧ k 0=0 ∧
        (∀t∈Icc (0:ℝ) 1,u t∈B.carrier ∧ u t=x+(extendPath f t-extendPath f 0)+k t) ∧
        TendstoUniformlyOn (fun m => mesh B x (extendPath f) (m+1)) u atTop (Icc 0 1) ∧
        BoundedVariationOn k (Icc (0:ℝ) 1) ∧ NormalPartitionCondition B u k ∧
        IsFiniteMeasure ν.variation ∧ ν ({0}:Set unitInterval)=0 ∧
        (∀a b : unitInterval,a≤b → ν (Ioc a b)=k b-k a) ∧
        ∀y : unitInterval → E,Continuous y → (∀t,y t∈B.carrier) →
          ν.integral (fun t => u t-y t) (innerSL ℝ) ≤ 0 := by
  classical
  have hc (f : VectorPath E) : ContinuousOn (extendPath f) (Icc (0:ℝ) 1) :=
    (f.continuous.comp continuous_projIcc).continuousOn
  have hex (f : VectorPath E) : ∃u : ℝ → E,ContinuousOn u (Icc (0:ℝ) 1) ∧
      TendstoUniformlyOn (fun n => mesh B x (extendPath f) (n+1)) u atTop (Icc 0 1) := by
    obtain ⟨u,k,ν,hu,hk,hu0,hk0,hbody,hconv,hrest⟩ :=
      reflected_equation B x c r R hx hr hball hR (extendPath f) (hc f)
    exact ⟨u,hu,hconv⟩
  choose u hu hconv using hex
  let Φ : VectorPath E → VectorPath E := fun f =>
    ⟨fun t => u f t,continuousOn_iff_continuous_domRestrict.mp (hu f)⟩
  have hcont : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    intro f
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨z,hz,hBz,hzconv,hd⟩ :=
      reflected_driver_continuity B x c r R hx hr hball hR (extendPath f) (hc f)
    obtain ⟨δ,hδ,hclose⟩ := hd ε hε
    refine ⟨δ,hδ,?_⟩
    intro g hg
    have htube (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : ‖extendPath g t-extendPath f t‖<δ := by
      have hh := (ContinuousMap.norm_lt_iff (g-f) hδ).mp (by simpa [dist_eq_norm] using hg)
      exact hh (Set.projIcc 0 1 (by norm_num) t)
    obtain ⟨v,hv,hBv,hvconv,hbound⟩ := hclose (extendPath g) (hc g) htube
    rw [dist_eq_norm,ContinuousMap.norm_lt_iff _ hε]
    intro t
    have hf : u f t=z t := tendsto_nhds_unique ((hconv f).tendsto_at t.2) (hzconv.tendsto_at t.2)
    have hg' : u g t=v t := tendsto_nhds_unique ((hconv g).tendsto_at t.2) (hvconv.tendsto_at t.2)
    change ‖u g t-u f t‖<ε
    rw [hf,hg']
    exact lt_of_le_of_lt (le_add_of_nonneg_right (norm_nonneg _)) (hbound t t.2)
  refine ⟨Φ,hcont,hcont.measurable,?_⟩
  intro f
  obtain ⟨v,k,ν,hv,hk,hv0,hk0,hbody,hvconv,hrest⟩ :=
    reflected_equation B x c r R hx hr hball hR (extendPath f) (hc f)
  refine ⟨v,k,ν,?_,hv,hk,hv0,hk0,hbody,hvconv,hrest⟩
  intro t
  exact tendsto_nhds_unique ((hconv f).tendsto_at t.2) (hvconv.tendsto_at t.2)

end BrownianForcing

end OAI
