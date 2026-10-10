import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodMap

namespace OAI

namespace BrownianForcing

open MeasureTheory Set Filter ConvexSkorokhod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def IsReflectedMap (B : Body E) (x : E) (Φ : VectorPath E → VectorPath E) : Prop :=
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
      ν.integral (fun t => u t-y t) (innerSL ℝ) ≤ 0

noncomputable def normalImpulse (n : E) (p : VectorPath E × VectorPath E) : ℝ :=
  inner ℝ n ((p.2 halfTime-p.2 lastTime)-(p.1 halfTime-p.1 lastTime))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma extendPath_apply (f : VectorPath E) (t : Set.Icc (0:ℝ) 1) : extendPath f t=f t := by
  dsimp [extendPath]
  rw [Set.projIcc_of_mem _ t.2]

end BrownianForcing

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set Filter ConvexSkorokhod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem reflected_law_facet_force
    (μ : Measure (VectorPath E)) [IsGaussian μ] (hμ : (∫ f, f ∂μ)=0)
    (hcov : ∀ (s t : Set.Icc (0:ℝ) 1) (v w : E),
      cov[scalarEval s v,scalarEval t w;μ] = 2*min (s:ℝ) (t:ℝ)*inner ℝ v w)
    (B : Body E) (x y n c : E) (a r R : ℝ)
    (hx : x∈B.carrier) (hy : y∈B.carrier) (hn : ‖n‖=1)
    (hsupport : ∀z∈B.carrier,inner ℝ n (z-y) ≤ 0)
    (ha : 0<a) (hr : 0<r)
    (hball : Metric.closedBall c r⊆B.carrier) (hR : ∀z∈B.carrier,‖z-c‖≤R) :
    ∃Φ : VectorPath E → VectorPath E,Continuous Φ ∧ IsReflectedMap B x Φ ∧
      ∃ν : Measure (VectorPath E × VectorPath E),IsProbabilityMeasure ν ∧
        ν=μ.map (fun f => (f,Φ f)) ∧ ν.map Prod.fst=μ ∧
        0<ν {p | a/2<normalImpulse n p} := by
  obtain ⟨Φ,hΦcont,hΦmeas,hΦ⟩ := measurable_reflected_path_map B x c r R hx hr hball hR
  have hpair : Measurable (fun f : VectorPath E => (f,Φ f)) := measurable_id.prodMk hΦmeas
  let ν := μ.map (fun f : VectorPath E => (f,Φ f))
  have hνprob : IsProbabilityMeasure ν := inferInstance
  refine ⟨Φ,hΦcont,hΦ,ν,hνprob,rfl,?_,?_⟩
  · rw [Measure.map_map measurable_fst hpair]
    simp [Function.comp_def]
  · have hE : MeasurableSet {p : VectorPath E × VectorPath E | a/2<normalImpulse n p} := by
      apply IsOpen.measurableSet
      apply isOpen_lt continuous_const
      change Continuous (fun p : VectorPath E × VectorPath E =>
        inner ℝ n ((p.2 halfTime-p.2 lastTime)-(p.1 halfTime-p.1 lastTime)))
      fun_prop
    rw [Measure.map_apply hpair hE]
    obtain ⟨S,hS,hpos,hforce⟩ := brownian_supporting_facet_force μ hμ hcov B x y n c a r R 1
      hx hy hn hsupport ha hr zero_lt_one hball hR
    apply hpos.trans_le
    apply measure_mono
    intro f hf
    obtain ⟨u,k,hu,hk,hu0,hk0,hbody,hconv,hbv,hnorm,hclose,himp⟩ := hforce f hf
    obtain ⟨v,l,ζ,hvalues,hv,hl,hv0,hl0,hbodyv,hconvv,hrest⟩ := hΦ f
    have hvaluesu (t : Set.Icc (0:ℝ) 1) : Φ f t=u t := by
      rw [hvalues]
      exact tendsto_nhds_unique (hconvv.tendsto_at t.2) (hconv.tendsto_at t.2)
    have huH := (hbody halfTime halfTime.2).2
    have huL := (hbody lastTime lastTime.2).2
    rw [extendPath_apply] at huH huL
    change a/2<normalImpulse n (f,Φ f)
    dsimp [normalImpulse]
    rw [hvaluesu,hvaluesu,huH,huL]
    convert himp using 1; congr 1; dsimp [halfTime,lastTime]; abel

end BrownianForcing

end OAI
