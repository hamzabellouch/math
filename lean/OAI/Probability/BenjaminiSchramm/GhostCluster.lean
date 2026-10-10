import OAI.Probability.BenjaminiSchramm.GhostField
import OAI.Probability.BenjaminiSchramm.TiltedGhostSusceptibility

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm

variable {V E : Type*} (G : BondGraph V E)

def quarterGhostWeight (x y : V) : ℝ≥0 :=
  (G.stabilizerWeight x y ^ (1 / 4 : ℝ)).toNNReal

lemma coe_quarterGhostWeight (x y : V) :
    (G.quarterGhostWeight x y : ℝ≥0∞) = G.stabilizerWeight x y ^ (1 / 4 : ℝ) := by
  exact ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (G.stabilizerWeight_ne_top x y))

lemma quarterGhostWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x v y : V) : G.quarterGhostWeight x y =
      G.quarterGhostWeight x v * G.quarterGhostWeight v y := by
  apply ENNReal.coe_injective
  rw [ENNReal.coe_mul, G.coe_quarterGhostWeight, G.coe_quarterGhostWeight,
    G.coe_quarterGhostWeight, G.stabilizerWeight_change_base hc hl x v y,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

lemma quarterGhostField_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (h : ℝ≥0) (x v : V) :
    ghostFieldLaw h (G.quarterGhostWeight x) =
      ghostFieldLaw (h * G.quarterGhostWeight x v) (G.quarterGhostWeight v) := by
  unfold ghostFieldLaw
  congr 1
  funext y
  apply Subtype.ext
  simp only [ghostRate, ghostKernel, NNReal.coe_mul, G.quarterGhostWeight_change_base hc hl x v y]
  congr 2
  ring

lemma quarterTiltedMass_finite_sum {ω : Set E} {x : V} (hfin : (G.cluster ω x).Finite) :
    G.quarterTiltedMass ω x =
      ∑ y ∈ hfin.toFinset, (G.quarterGhostWeight x y : ℝ≥0∞) := by
  unfold quarterTiltedMass
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · apply Finset.sum_congr rfl
    intro y hy
    have hr : (G.openGraph ω).Reachable x y := hfin.mem_toFinset.mp hy
    rw [ite_eq_left hr, G.coe_quarterGhostWeight]
  · intro y hy
    exact ite_eq_right (fun hr => hy (hfin.mem_toFinset.mpr hr))

lemma quarterTiltedMass_toReal_finite_sum {ω : Set E} {x : V}
    (hfin : (G.cluster ω x).Finite) :
    (G.quarterTiltedMass ω x).toReal =
      ∑ y ∈ hfin.toFinset, (G.quarterGhostWeight x y : ℝ) := by
  rw [G.quarterTiltedMass_finite_sum hfin, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro y _
    exact ENNReal.coe_toReal _
  · intro y _
    exact ENNReal.coe_ne_top

lemma ghost_hit_cluster_joint_measurable [Countable V] [Countable E] (x : V) :
    MeasurableSet {z : Set E × Set V | ∃ y, (G.openGraph z.1).Reachable x y ∧ y ∈ z.2} := by
  exact (Measurable.exists fun y =>
    ((G.measurable_reachable x y).comp measurable_fst).and
      ((measurable_set_mem y).comp measurable_snd)).setOf

theorem quarterGhostField_hit_cluster [Countable V] (h : ℝ≥0) {ω : Set E} {x : V}
    (hfin : (G.cluster ω x).Finite) :
    (ghostFieldLaw h (G.quarterGhostWeight x)).real (ghostHits (G.cluster ω x)) =
      ghostKernel h (G.quarterTiltedMass ω x).toReal := by
  rw [G.quarterTiltedMass_toReal_finite_sum hfin]
  convert ghostFieldLaw_real_hit_finset h (G.quarterGhostWeight x) hfin.toFinset using 1
  rw [hfin.coe_toFinset]

theorem quarterTwoGhostField_hit_cluster [Countable V] (h : ℝ≥0) {ω : Set E} {x : V}
    (hfin : (G.cluster ω x).Finite) :
    ((ghostFieldLaw h (G.quarterGhostWeight x)).prod
      (ghostFieldLaw h (G.quarterGhostWeight x))).real
      (ghostHits (G.cluster ω x) ×ˢ ghostHits (G.cluster ω x)) =
        ghostKernel h (G.quarterTiltedMass ω x).toReal ^ 2 := by
  rw [G.quarterTiltedMass_toReal_finite_sum hfin]
  convert twoGhostFieldLaw_real_hit_finset h (G.quarterGhostWeight x) hfin.toFinset using 1
  rw [hfin.coe_toFinset]

theorem quarterGhostConnection_average [Countable V] [Countable E]
    (p : unitInterval) (x : V) (h : ℝ≥0)
    (hfin : ∀ᵐ ω ∂G.law p, (G.cluster ω x).Finite) :
    (∫⁻ m, G.law p {ω | ∃ y ∈ m, (G.openGraph ω).Reachable x y}
      ∂ghostFieldLaw h (G.quarterGhostWeight x)) =
        ENNReal.ofReal (G.quarterGhostMagnetization p x h) := by
  let ν := ghostFieldLaw h (G.quarterGhostWeight x)
  let A := {z : Set E × Set V | ∃ y, (G.openGraph z.1).Reachable x y ∧ y ∈ z.2}
  have hm : MeasurableSet A := G.ghost_hit_cluster_joint_measurable x
  have he := (Measure.prod_apply (μ := G.law p) (ν := ν) hm).symm.trans
    (Measure.prod_apply_symm (μ := G.law p) (ν := ν) hm)
  have hswap : (∫⁻ m, G.law p {ω | ∃ y ∈ m, (G.openGraph ω).Reachable x y} ∂ν) =
      ∫⁻ ω, ν (ghostHits (G.cluster ω x)) ∂G.law p := by
    convert he.symm using 1
    · apply lintegral_congr
      intro m
      congr 1
      ext ω
      simp only [A, Set.mem_preimage, Set.mem_ofPred_eq]
      exact exists_congr (fun y => and_comm)
    · rfl
  rw [hswap]
  have hprob : (fun ω => ν (ghostHits (G.cluster ω x))) =ᵐ[G.law p]
      (fun ω => ENNReal.ofReal (ghostKernel h (G.quarterTiltedMass ω x).toReal)) := by
    filter_upwards [hfin] with ω hω
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact congrArg ENNReal.ofReal (G.quarterGhostField_hit_cluster h hω)
  rw [lintegral_congr_ae hprob]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_ghostKernel (G.law p) _ (G.measurable_quarterTiltedMass x).ennreal_toReal
      (fun _ => ENNReal.toReal_nonneg) h.2)
    (ae_of_all _ fun _ => ghostKernel_nonneg h.2 ENNReal.toReal_nonneg)).symm

theorem quarterGhostConnection_change_base [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : unitInterval) (x v : V) (h : ℝ≥0)
    (hfin : ∀ᵐ ω ∂G.law p, (G.cluster ω v).Finite) :
    (∫⁻ m, G.law p {ω | ∃ y ∈ m, (G.openGraph ω).Reachable v y}
      ∂ghostFieldLaw h (G.quarterGhostWeight x)) =
        ENNReal.ofReal (G.quarterGhostMagnetization p v (h * G.quarterGhostWeight x v)) := by
  rw [G.quarterGhostField_change_base hc hl h x v]
  exact G.quarterGhostConnection_average p v _ hfin

end CriticalPercolation.BondGraph

end

end OAI
