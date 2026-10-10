import OAI.Probability.BenjaminiSchramm.GhostCluster

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem quarterTwoGhostConnection_average (p : unitInterval) (x : V) (h : ℝ≥0)
    (hfin : ∀ᵐ ω ∂G.law p, (G.cluster ω x).Finite) :
    (∫⁻ m, ∫⁻ n, G.law p {ω |
      (∃ y ∈ m, (G.openGraph ω).Reachable x y) ∧
      (∃ y ∈ n, (G.openGraph ω).Reachable x y)}
      ∂ghostFieldLaw h (G.quarterGhostWeight x)
      ∂ghostFieldLaw h (G.quarterGhostWeight x)) =
      ENNReal.ofReal (∫ ω, ghostKernel h (G.quarterTiltedMass ω x).toReal ^ 2 ∂G.law p) := by
  let ν := ghostFieldLaw h (G.quarterGhostWeight x)
  let A := {z : Set E × (Set V × Set V) |
    (∃ y, (G.openGraph z.1).Reachable x y ∧ y ∈ z.2.1) ∧
    (∃ y, (G.openGraph z.1).Reachable x y ∧ y ∈ z.2.2)}
  have hm : MeasurableSet A := by
    have h₁ : Measurable (fun z : Set E × (Set V × Set V) =>
        ∃ y, (G.openGraph z.1).Reachable x y ∧ y ∈ z.2.1) :=
      Measurable.exists fun y => ((G.measurable_reachable x y).comp measurable_fst).and
        ((measurable_set_mem y).comp (measurable_fst.comp measurable_snd))
    have h₂ : Measurable (fun z : Set E × (Set V × Set V) =>
        ∃ y, (G.openGraph z.1).Reachable x y ∧ y ∈ z.2.2) :=
      Measurable.exists fun y => ((G.measurable_reachable x y).comp measurable_fst).and
        ((measurable_set_mem y).comp (measurable_snd.comp measurable_snd))
    exact (h₁.and h₂).setOf
  have hswap := (Measure.prod_apply (μ := G.law p) (ν := ν.prod ν) hm).symm.trans
    (Measure.prod_apply_symm (μ := G.law p) (ν := ν.prod ν) hm)
  have hmeas : Measurable (fun z : Set V × Set V => G.law p ((fun ω : Set E => (ω,z)) ⁻¹' A)) :=
    measurable_measure_prodMk_right hm
  have hmeas' : Measurable (fun z : Set V × Set V => G.law p {ω |
      (∃ y ∈ z.1, (G.openGraph ω).Reachable x y) ∧
      (∃ y ∈ z.2, (G.openGraph ω).Reachable x y)}) := by
    convert hmeas using 1
    funext z
    congr 1
    ext ω
    simp only [A, Set.mem_preimage, Set.mem_ofPred_eq]
    exact and_congr (exists_congr fun y => and_comm) (exists_congr fun y => and_comm)
  have he : (∫⁻ m, ∫⁻ n, G.law p {ω |
      (∃ y ∈ m, (G.openGraph ω).Reachable x y) ∧
      (∃ y ∈ n, (G.openGraph ω).Reachable x y)} ∂ν ∂ν) =
      ∫⁻ ω, (ν.prod ν) (ghostHits (G.cluster ω x) ×ˢ ghostHits (G.cluster ω x)) ∂G.law p := by
    rw [← lintegral_prod _ hmeas'.aemeasurable]
    convert hswap.symm using 1
    · apply lintegral_congr
      intro z
      congr 1
      ext ω
      simp only [A, Set.mem_preimage, Set.mem_ofPred_eq]
      exact and_congr (exists_congr fun y => and_comm) (exists_congr fun y => and_comm)
    · rfl
  rw [he]
  have hprob : (fun ω => (ν.prod ν) (ghostHits (G.cluster ω x) ×ˢ ghostHits (G.cluster ω x)))
      =ᵐ[G.law p] (fun ω => ENNReal.ofReal (ghostKernel h (G.quarterTiltedMass ω x).toReal ^ 2)) := by
    filter_upwards [hfin] with ω hω
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact congrArg ENNReal.ofReal (G.quarterTwoGhostField_hit_cluster h hω)
  rw [lintegral_congr_ae hprob]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_ghostKernel_sq (G.law p) _ (G.measurable_quarterTiltedMass x).ennreal_toReal
      (fun _ => ENNReal.toReal_nonneg) h.2)
    (ae_of_all _ fun _ => sq_nonneg _)).symm

end CriticalPercolation.BondGraph

end

end OAI
