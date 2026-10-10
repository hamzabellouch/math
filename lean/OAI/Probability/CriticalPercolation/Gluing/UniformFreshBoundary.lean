import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.BallIncidence
import OAI.Probability.CriticalPercolation.Criticality.CylinderApproximation
import OAI.Probability.CriticalPercolation.Exploration.FrontierDivergence
import OAI.Probability.CriticalPercolation.Exploration.OpenFrontierDivergence
import OAI.Probability.CriticalPercolation.Exploration.SliceExploration

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal symmDiff Topology

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma smallFreshBoundary_uniform_finite
    (hl : G.LocallyFinite) (p : unitInterval) (hp : (p:ℝ)<1)
    (v : V) (M : ℕ) (b : ℝ) (hb : 0<b) :
    ∃ S : Finset E, ∀ X : Set E, (S:Set E)⊆X →
      (G.law p).real (G.infiniteEvent v ∩ G.smallFreshBoundary X v M)<b := by
  let r : ℝ := (1-(p:ℝ))^M
  have hr : 0<r := pow_pos (sub_pos.mpr hp) _
  have hδ : 0<b*r/(1+r) := div_pos (mul_pos hb hr) (by linarith)
  obtain ⟨S,H,hH,happrox⟩ := exists_finiteCoordinate_approx (fun _ : E => p)
    (G.measurableSet_infiniteEvent v) (ENNReal.ofReal_pos.mpr hδ)
  have hreal : (G.law p).real (H ∆ G.infiniteEvent v)<b*r/(1+r) := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr happrox
    simpa only [law_const,ENNReal.toReal_ofReal hδ.le,Measure.real,law] using hh
  refine ⟨S,fun X hX => ?_⟩
  have hh := G.smallFreshBoundary_approx_bound hl p X v M H (blockSigma_mono hX _ hH)
  change r*(G.law p).real (G.infiniteEvent v ∩ G.smallFreshBoundary X v M) ≤
    (1+r)*(G.law p).real (H ∆ G.infiniteEvent v) at hh
  have hmul := mul_lt_mul_of_pos_left hreal (show 0<1+r by linarith)
  rw [mul_div_cancel₀ _ (ne_of_gt (show 0<1+r by linarith))] at hmul
  nlinarith only [hh,hmul,hr]

theorem fewOpenFreshBoundary_uniform_finite
    (hl : G.LocallyFinite) (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (v : V) (N : ℕ) (b : ℝ) (hb : 0<b) :
    ∃ S : Finset E, ∀ X : Set E, (S:Set E)⊆X →
      (G.law p).real (G.infiniteEvent v ∩ G.fewOpenFreshBoundary X v N)<b := by
  have hpow : Tendsto (fun L : ℕ => (N+1:ℝ)*(1-(p:ℝ))^L) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (sub_nonneg.mpr p.2.2) (by linarith : 1-(p:ℝ)<1)).const_mul (N+1:ℝ)
  obtain ⟨L,hL⟩ := (hpow.eventually (gt_mem_nhds (half_pos hb))).exists
  obtain ⟨S,hS⟩ := G.smallFreshBoundary_uniform_finite hl p hp1 v ((N+1)*L)
    (b/2) (half_pos hb)
  refine ⟨S,fun X hX => ?_⟩
  have ht := G.fewOpenFreshBoundary_probability_le hl p X v N L
  have hs := hS X hX
  linarith

omit [Countable V] [Countable E] in
lemma Aut.cutEdges_image (φ : G.Aut) (S : Set V) :
    φ.edge '' G.cutEdges S=G.cutEdges (φ.vertex '' S) := by
  ext e
  obtain ⟨e,rfl⟩ := φ.edge.surjective e
  constructor
  · rintro ⟨f,⟨x,y,he,hx,hy⟩,hef⟩
    have hfe : f=e := φ.edge.injective hef
    subst f
    refine ⟨φ.vertex x,φ.vertex y,?_,?_,⟨y,hy,rfl⟩⟩
    · rw [φ.preserves,he,Sym2.map_mk]
    · simpa only [Set.mem_image_equiv,Equiv.symm_apply_apply] using hx
  · rintro ⟨x,y,he,hx,hy⟩
    obtain ⟨a,rfl⟩ := φ.vertex.surjective x
    obtain ⟨b,rfl⟩ := φ.vertex.surjective y
    refine ⟨e,⟨a,b,?_,?_,?_⟩,rfl⟩
    · rw [φ.preserves,←Sym2.map_mk] at he
      exact Sym2.map.injective φ.vertex.injective he
    · simpa only [Set.mem_image_equiv,Equiv.symm_apply_apply] using hx
    · simpa only [Set.mem_image_equiv,Equiv.symm_apply_apply] using hy

omit [Countable V] [Countable E] in
lemma Aut.freshClusterBoundary_image (φ : G.Aut) (X ω : Set E) (v : V) :
    φ.edge '' G.freshClusterBoundary X v ω =
      G.freshClusterBoundary (φ.edge '' X) (φ.vertex v) (φ.edge '' ω) := by
  unfold freshClusterBoundary
  rw [Set.image_sdiff φ.edge.injective,φ.cutEdges_image,φ.cluster_image,
    Set.image_inter φ.edge.injective]

lemma measurableSet_fewOpenFreshBoundary (X : Set E) (v : V) (N : ℕ) :
    MeasurableSet (G.fewOpenFreshBoundary X v N) := by
  have hi : Measurable (fun ω : Set E => ω∩X) :=
    (measurable_inter_block X).mono (blockSigma_le X) le_rfl
  have hf : MeasurableSet {ω : Set E | (G.cluster (ω∩X) v).Finite} := by
    simpa only [Function.comp_apply,Set.not_infinite] using
      (((G.measurable_infinite_cluster v).comp hi).not).setOf
  have hb : Measurable (fun ω : Set E => G.freshClusterBoundary X v ω∩ω) := by
    apply Measurable.of_eval
    intro e
    exact ((measurable_pi_apply e).comp
      ((G.measurable_freshClusterBoundary X v).mono (blockSigma_le X) le_rfl)).and
      (measurable_set_mem e)
  exact hf.inter (measurableSet_Iic.preimage (measurable_ncard.comp hb))

omit [Countable V] [Countable E] in
lemma Aut.fewOpenFreshBoundary_preimage (φ : G.Aut) (X : Set E) (v : V) (N : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹'
      G.fewOpenFreshBoundary (φ.edge '' X) (φ.vertex v) N =
        G.fewOpenFreshBoundary X v N := by
  ext ω
  change ((G.cluster ((φ.edge '' ω)∩(φ.edge '' X)) (φ.vertex v)).Finite ∧ _) ↔ _
  rw [←Set.image_inter φ.edge.injective,←φ.cluster_image,
    ←φ.freshClusterBoundary_image,←Set.image_inter φ.edge.injective,
    Set.finite_image_iff φ.vertex.injective.injOn,
    Set.ncard_image_of_injective _ φ.edge.injective]
  rfl

lemma Aut.infinite_fewOpen_real (φ : G.Aut) (p : unitInterval)
    (X : Set E) (v : V) (N : ℕ) :
    (G.law p).real (G.infiniteEvent (φ.vertex v) ∩
      G.fewOpenFreshBoundary (φ.edge '' X) (φ.vertex v) N) =
    (G.law p).real (G.infiniteEvent v ∩ G.fewOpenFreshBoundary X v N) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (measurable_image_equiv φ.edge)
    ((G.measurableSet_infiniteEvent _).inter (G.measurableSet_fewOpenFreshBoundary _ _ _)),
    Set.preimage_inter,φ.preimage_infiniteEvent,φ.fewOpenFreshBoundary_preimage]

theorem fewOpenFreshBoundary_uniform_ball
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (N : ℕ) (b : ℝ) (hb : 0<b) :
    ∃ R : ℕ, ∀ v : V, ∀ X : Set E, G.inducedEdges (G.vertexBall v R)⊆X →
      (G.law p).real (G.infiniteEvent v ∩ G.fewOpenFreshBoundary X v N)<b := by
  obtain ⟨S,hS,hcover⟩ := hq
  have hh (s : S) : ∃ R : ℕ, ∀ X : Set E, G.inducedEdges (G.vertexBall s.val R)⊆X →
      (G.law p).real (G.infiniteEvent s.val ∩ G.fewOpenFreshBoundary X s.val N)<b := by
    obtain ⟨F,hF⟩ := G.fewOpenFreshBoundary_uniform_finite hl p hp hp1 s N b hb
    obtain ⟨R,hR⟩ := G.finite_bonds_in_ball hc s F.finite_toSet
    exact ⟨R,fun X hX => hF X (hR.trans hX)⟩
  choose R hR using hh
  let := hS.fintype
  let L := ∑ s : S, R s
  refine ⟨L,fun v X hX => ?_⟩
  obtain ⟨s,hs,φ,rfl⟩ := hcover v
  let Y : Set E := φ.edge ⁻¹' X
  have he : φ.edge '' Y=X := Set.image_preimage_eq _ φ.edge.surjective
  rw [←he,φ.infinite_fewOpen_real]
  apply hR ⟨s,hs⟩ Y
  intro e hee
  apply hX
  have hball : G.vertexBall s (R ⟨s,hs⟩)⊆G.vertexBall s L :=
    G.vertexBall_mono s (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨s,hs⟩ : S)))
  have hh := Aut.inducedEdges_map G φ (G.inducedEdges_monotone hball)
    (show φ.edge e∈φ.edge '' G.inducedEdges (G.vertexBall s (R ⟨s,hs⟩)) from ⟨e,hee,rfl⟩)
  rwa [Aut.vertexBall_image] at hh

end CriticalPercolation.BondGraph
end
end

end OAI
