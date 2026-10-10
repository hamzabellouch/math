import Mathlib
import OAI.Probability.LatticeSurface.Brownian.BrownianClock
import OAI.Probability.LatticeSurface.Brownian.BrownianFacet

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set Filter ConvexSkorokhod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem shortClock_supporting_facet_force
    (μ : Measure (VectorPath E)) [IsGaussian μ] (hμ : (∫ f, f ∂μ)=0)
    (τ : ℝ) (hτ : 0<τ)
    (hcov : ∀ (s t : Set.Icc (0:ℝ) 1) (v w : E),
      cov[scalarEval s v,scalarEval t w;μ] = (2*τ)*min (s:ℝ) (t:ℝ)*inner ℝ v w)
    (B : Body E) (x y n c : E) (a r R ε : ℝ)
    (hx : x∈B.carrier) (hy : y∈B.carrier) (hn : ‖n‖=1)
    (hsupport : ∀z∈B.carrier,inner ℝ n (z-y) ≤ 0)
    (ha : 0<a) (hr : 0<r) (hε : 0<ε)
    (hball : Metric.closedBall c r⊆B.carrier) (hR : ∀z∈B.carrier,‖z-c‖≤R) :
    ∃S : Set (VectorPath E),MeasurableSet S ∧ 0<μ S ∧ ∀f∈S,
      ∃u k : ℝ → E,ContinuousOn u (Icc 0 1) ∧ ContinuousOn k (Icc 0 1) ∧
        u 0=x ∧ k 0=0 ∧
        (∀t∈Icc (0:ℝ) 1,u t∈B.carrier ∧ u t=x+(extendPath f t-extendPath f 0)+k t) ∧
        TendstoUniformlyOn (fun m => mesh B x (extendPath f) (m+1)) u atTop (Icc 0 1) ∧
        BoundedVariationOn k (Icc (0:ℝ) 1) ∧ NormalPartitionCondition B u k ∧
        (∀t∈Icc (0:ℝ) 1,‖u t-facetPath x y t‖ < ε) ∧
        a/2 < inner ℝ n (k (1/2)-k 1) := by
  obtain ⟨δ,hδ,hforce⟩ := facet_forcing_tube B x y n c a r R ε hx hy hn hsupport ha hr hε hball hR
  let S : Set (VectorPath E) := {f | ∀t : Set.Icc (0:ℝ) 1,‖f t-twoPieceVector (y-x) (a • n) t‖<δ}
  have hset : S=Metric.ball (twoPieceVector (y-x) (a • n)) δ := by
    ext f
    simp only [S,mem_ofPred_eq,Metric.mem_ball,dist_eq_norm]
    rw [ContinuousMap.norm_lt_iff _ hδ]
    simp only [ContinuousMap.sub_apply]
  refine ⟨S,?_,shortClock_twoPiece_tube μ hμ τ hτ hcov (y-x) (a • n) δ hδ,?_⟩
  · rw [hset]
    exact Metric.isOpen_ball.measurableSet
  · intro f hf
    apply hforce (extendPath f) ((f.continuous.comp continuous_projIcc).continuousOn)
    intro t ht
    dsimp [extendPath]
    rw [Set.projIcc_of_mem _ ht]
    simpa [twoPieceVector,facetDriver] using hf ⟨t,ht⟩

end BrownianForcing

end OAI
