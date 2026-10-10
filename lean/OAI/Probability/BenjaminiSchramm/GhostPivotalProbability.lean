import OAI.Probability.BenjaminiSchramm.GhostPivotalGeometry
import OAI.Probability.BenjaminiSchramm.GhostPivotalBound
import OAI.Probability.BenjaminiSchramm.PivotalExposure
import OAI.Probability.BenjaminiSchramm.PhaseInput

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma criticalModel_eraseVertices (ω : Set E) (S : Set V) :
    (criticalModel G).eraseVertices ω S = ω ∩ internalEdges G Sᶜ := by
  ext e
  simp only [CriticalPercolation.BondGraph.eraseVertices,
    CriticalPercolation.BondGraph.incidentEdges, criticalModel, Set.mem_sdiff,
    Set.mem_inter_iff, internalEdges, Set.mem_ofPred_eq, Set.mem_compl_iff,
    not_exists, not_and]
  constructor
  · rintro ⟨he,h⟩
    exact ⟨he,fun y hy hS => h y hS hy⟩
  · rintro ⟨he,h⟩
    exact ⟨he,fun y hS hy => h y hy hS⟩

omit [Countable V] [Countable E] in
lemma force_closed_eq_sdiff (ω : Set E) (e : E) :
    CriticalPercolation.BernoulliProduct.forceOn {e} ∅ ω = ω \ {e} := by
  ext f
  by_cases hf : f = e <;> simp [hf]

lemma measurableSet_ghostBridge_fixed_cluster (S : Set V) (x : V) (e : E) (u v : V)
    (m n : Set V) :
    MeasurableSet {ω | GhostBridgePivotal G ω m n x e u v ∧
      cluster G (ω \ {e}) x = S} := by
  have hdel : Measurable (fun ω : Set E => ω \ {e}) :=
    measurable_set_iff.mpr fun f => (measurable_set_mem f).and measurable_const
  have hp := (measurableSet_ghostBridgePivotal G x e u v).preimage
    (show Measurable (fun ω : Set E => ((m,n),ω)) from
      measurable_const.prodMk measurable_id)
  have hc := ((criticalModel G).measurableSet_exactCluster x S).preimage hdel
  simpa only [Set.preimage_ofPred_eq, Set.mem_ofPred_eq, criticalModel_cluster] using (hp.mem.and hc.mem).setOf

theorem ghostBridge_fixed_cluster_measure_le (p : unitInterval) (hp : (p : ℝ) < 1)
    (S : Set V) (x : V) (e : E) (u v : V) (hends : G e = s(u,v))
    (hu : u ∈ S) (hv : v ∉ S) (m n : Set V) :
    law p {ω | GhostBridgePivotal G ω m n x e u v ∧ cluster G (ω \ {e}) x = S} ≤
      (ENNReal.ofReal (p : ℝ) / ENNReal.ofReal (1 - (p : ℝ))) *
        law p {ω | cluster G ω x = S} *
          (if Disjoint S m ∧ Disjoint S n then
            law p (DisjointOccurrence (finiteGhostConnection G v id m)
              (finiteGhostConnection G v id n)) else 0) := by
  let D := DisjointOccurrence (finiteGhostConnection G v id m) (finiteGhostConnection G v id n)
  have hD : MeasurableSet D := (measurableSet_ghostDisjointOccurrence G v id).preimage
    (show Measurable (fun ω : Set E => ((m,n),ω)) from
      measurable_const.prodMk measurable_id)
  let F := D.indicator (fun _ : Set E => (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator hD
  by_cases havoid : Disjoint S m ∧ Disjoint S n
  · rw [ite_eq_left havoid]
    have hpoint (ω : Set E) :
        ({ω | GhostBridgePivotal G ω m n x e u v ∧ cluster G (ω \ {e}) x = S} : Set (Set E)).indicator
          (fun _ => (1 : ℝ≥0∞)) ω ≤
        if e ∈ ω then ({η | (criticalModel G).cluster η x = S} : Set (Set E)).indicator
          (fun η => F ((criticalModel G).eraseVertices η S))
          (CriticalPercolation.BernoulliProduct.forceOn {e} ∅ ω) else 0 := by
      by_cases hω : GhostBridgePivotal G ω m n x e u v ∧ cluster G (ω \ {e}) x = S
      · have horig := hω
        obtain ⟨⟨he,_,_,hnot,_,_,hdo⟩,hcl⟩ := hω
        have hd := ghostDisjointOccurrence_exterior G x v m n hnot hdo
        rw [hcl] at hd
        have hcl' : (criticalModel G).cluster
            (CriticalPercolation.BernoulliProduct.forceOn {e} ∅ ω) x = S := by
          rw [force_closed_eq_sdiff, criticalModel_cluster, hcl]
        have hd' : (criticalModel G).eraseVertices
            (CriticalPercolation.BernoulliProduct.forceOn {e} ∅ ω) S ∈ D := by
          rw [force_closed_eq_sdiff, criticalModel_eraseVertices G]
          exact hd
        simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_left horig, ite_eq_left he,
          ite_eq_left hcl', F, ite_eq_left hd', le_refl]
      · simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_right hω]
        exact bot_le
    calc
      _ = ∫⁻ ω, ({ω | GhostBridgePivotal G ω m n x e u v ∧
          cluster G (ω \ {e}) x = S} : Set (Set E)).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂law p := by
        exact (lintegral_indicator_one (measurableSet_ghostBridge_fixed_cluster G S x e u v m n)).symm
      _ ≤ _ := lintegral_mono hpoint
      _ = _ := (criticalModel G).closed_cluster_pivotal_factor p hp x S e u v hends hu hv F hF
      _ ≤ _ := by
        simp only [criticalModel_cluster]
        apply mul_le_mul' le_rfl
        calc
          _ ≤ ∫⁻ η, F η ∂(criticalModel G).law p := by
            apply lintegral_mono
            intro η
            by_cases he : (criticalModel G).eraseVertices η S ∈ D
            · have he' : η ∈ D := (disjointOccurrence_upper _ _)
                (fun _ h => h.1) he
              simp only [F, Set.indicator, ite_eq_left he, ite_eq_left he', le_refl]
            · simp only [F, Set.indicator, ite_eq_right he]
              exact bot_le
          _ = _ := lintegral_indicator_one hD
  · have he : {ω | GhostBridgePivotal G ω m n x e u v ∧
        cluster G (ω \ {e}) x = S} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨h,hcl⟩
      exact havoid (by simpa only [← hcl] using ⟨h.2.2.2.2.1,h.2.2.2.2.2.1⟩)
    simp only [he,measure_empty,ite_eq_right havoid,mul_zero,le_refl]

theorem averaged_ghostBridge_fixed_cluster_le (p : unitInterval) (hp : (p : ℝ) < 1)
    (S : Finset V) (x : V) (e : E) (u v : V) (hends : G e = s(u,v))
    (hu : u ∈ S) (hv : v ∉ S) (h : ℝ≥0) (w : V → ℝ≥0) :
    (∫⁻ m, ∫⁻ n, law p {ω | GhostBridgePivotal G ω m n x e u v ∧
      cluster G (ω \ {e}) x = (S : Set V)} ∂ghostFieldLaw h w ∂ghostFieldLaw h w) ≤
      (ENNReal.ofReal (p : ℝ) / ENNReal.ofReal (1 - (p : ℝ))) *
        law p {ω | cluster G ω x = (S : Set V)} *
        (ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ y ∈ S, (w y : ℝ)))) ^ 2 *
        (∫⁻ m, law p (finiteGhostConnection G v id m) ∂ghostFieldLaw h w) ^ 2 := by
  let C := (ENNReal.ofReal (p : ℝ) / ENNReal.ofReal (1 - (p : ℝ))) *
    law p {ω | cluster G ω x = (S : Set V)}
  have hC : C ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · rw [div_eq_mul_inv]
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp)).ne'
    · exact measure_ne_top _ _
  calc
    _ ≤ ∫⁻ m, ∫⁻ n, C * (if Disjoint (S : Set V) m ∧ Disjoint (S : Set V) n then
        law p (DisjointOccurrence (finiteGhostConnection G v id m)
          (finiteGhostConnection G v id n)) else 0) ∂ghostFieldLaw h w ∂ghostFieldLaw h w := by
      apply lintegral_mono
      intro m
      apply lintegral_mono
      intro n
      exact ghostBridge_fixed_cluster_measure_le G p hp S x e u v hends hu hv m n
    _ = C * (∫⁻ m, ∫⁻ n, if Disjoint (S : Set V) m ∧ Disjoint (S : Set V) n then
        law p (DisjointOccurrence (finiteGhostConnection G v id m)
          (finiteGhostConnection G v id n)) else 0 ∂ghostFieldLaw h w ∂ghostFieldLaw h w) := by
      simp_rw [lintegral_const_mul' C _ hC]
    _ ≤ _ := by
      simpa only [C, mul_assoc] using mul_le_mul' (le_refl C)
        (ghost_avoidance_bk G p v h w S)

end Percolation.BenjaminiSchramm

end

end OAI
