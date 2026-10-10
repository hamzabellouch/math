import OAI.Geometry.CylinderCovering.Singular.EdgeOneCover
import OAI.Geometry.CylinderCovering.Singular.EdgeOneDifferential
import OAI.Geometry.CylinderCovering.Singular.Orthogonal

namespace OAI

noncomputable section
open Set MeasureTheory Filter Topology
namespace CylinderCovering.SingularEdgeOneCover
open RuledApproximation

lemma labelMap_image {p c d q : ℝ}
    (hcap : ∀ b ∈ FlexibleSingular.labelDomain p c d q, b 1 ≤ 1) :
    SingularEdgeOne.labelMap '' FlexibleSingular.labelDomain p c d q =
      labelDomain p (4*c) d q := by
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (label_dictionary hcap a).mpr ha
  · intro hb
    refine ⟨vec2 (2*b 0) (b 1),?_,label_expand_contract b⟩
    apply (label_dictionary hcap _).mp
    simpa only [label_expand_contract] using hb

lemma cost_dictionary {p c d q : ℝ} (hd : 0 < d)
    (hcap : ∀ b ∈ FlexibleSingular.labelDomain p c d q, b 1 ≤ 1) :
    cost p (4*c) d q = FlexibleSingular.cost p c d q/4 := by
  have he := SingularEdgeOne.physical_cost_dictionary p c
    (FlexibleSingular.labelDomain_isCompact p c d q).measurableSet
    (fun b hb => hd.trans_le hb.1)
  rw [labelMap_image hcap] at he
  exact he

lemma cost_dictionary_eventually {p : ℝ} {ρ q : ℝ → ℝ}
    (hadm : SingularCutoff.Admissible p ρ q) :
    ∀ᶠ k : ℝ in 𝓝[>] 0,
      cost p k (ρ (k/4)) (q (k/4)) =
        FlexibleSingular.cost p (k/4) (ρ (k/4)) (q (k/4))/4 := by
  filter_upwards [transport_zero_tendsto.eventually
    (FlexibleSingular.labelDomain_eq_upper_one hadm),
    transport_zero_tendsto.eventually hadm.1] with k hdom hpos
  have hcap : ∀ b ∈ FlexibleSingular.labelDomain p (k/4) (ρ (k/4)) (q (k/4)),
      b 1 ≤ 1 := by
    intro b hb
    rw [hdom] at hb
    exact hb.2.1
  have h := cost_dictionary hpos.1 hcap
  simpa only [show 4*(k/4)=k by ring] using h

lemma cost_quotient_tendsto {p : ℝ} {ρ q : ℝ → ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hadm : SingularCutoff.Admissible p ρ q) :
    Tendsto (fun k : ℝ =>
      (cost p k (ρ (k/4)) (q (k/4))/height-1/8)/k^2)
      (𝓝[>] 0) (𝓝 (singularCoefficient p/32)) := by
  have h := ((FlexibleSingular.weighted_integral_tendsto hp hp2 hadm).comp
    transport_zero_tendsto).div_const 32
  apply h.congr'
  filter_upwards [cost_dictionary_eventually hadm,self_mem_nhdsWithin] with k hk hk0
  have hk0 : k ≠ 0 := ne_of_gt hk0
  dsimp only [Function.comp_apply]
  rw [hk,height_eq]
  unfold FlexibleSingular.cost
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  ring

lemma cost_asymptotic {p : ℝ} {ρ q : ℝ → ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hadm : SingularCutoff.Admissible p ρ q) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun k => cost p k (ρ (k/4)) (q (k/4))/height-
        (1/8+singularCoefficient p/32*k^2)) (fun k => k^2) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have h := (cost_quotient_tendsto hp hp2 hadm).sub_const (singularCoefficient p/32)
    simp only [sub_self] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with k hk
    have hk0 : k ≠ 0 := ne_of_gt hk
    field_simp
    ring
  · filter_upwards [self_mem_nhdsWithin] with k hk
    exact fun h => False.elim ((pow_ne_zero 2 (ne_of_gt hk)) h)

lemma totalCost_small {p : ℝ} {ρ q : ℝ → ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hadm : SingularCutoff.Admissible p ρ q)
    (hcoef : singularCoefficient p < 0) :
    ∀ᶠ k : ℝ in 𝓝[>] 0,
      2*cost p k (ρ (k/4)) (q (k/4))+4*height*(ρ (k/4))^2 < height/4 := by
  filter_upwards [cost_dictionary_eventually hadm,
    transport_zero_tendsto.eventually (FlexibleSingular.totalCost_small hp hp2 hadm hcoef)]
    with k hdict hsmall
  rw [hdict,height_eq]
  nlinarith only [hsmall]

lemma finite_families_eventually {p : ℝ} {ρ q : ℝ → ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hadm : SingularCutoff.Admissible p ρ q) :
    ∀ᶠ k : ℝ in 𝓝[>] 0, ∀ e : ℝ, 0 < e →
      HasFiniteCover Cylinder.parallelogram (lowerFamily p k (ρ (k/4)) (q (k/4)))
        (cost p k (ρ (k/4)) (q (k/4))+e) ∧
      HasFiniteCover Cylinder.parallelogram (upperFamily p k (ρ (k/4)) (q (k/4)))
        (cost p k (ρ (k/4)) (q (k/4))+e) := by
  filter_upwards [cost_dictionary_eventually hadm,
    transport_zero_tendsto.eventually (FlexibleSingular.orthogonal_families_eventually hp hp2 hadm),
    transport_zero_tendsto.eventually (FlexibleSingular.labelDomain_eq_upper_one hadm),
    transport_zero_tendsto.eventually hadm.1] with k hdict hfam hdom hpos
  have hcap : ∀ b ∈ FlexibleSingular.labelDomain p (k/4) (ρ (k/4)) (q (k/4)),
      b 1 ≤ 1 := by
    intro b hb
    rw [hdom] at hb
    exact hb.2.1
  intro e he
  obtain ⟨hlow,hupp⟩ := hfam (4*e) (by positivity)
  have hl := hlow.parallelogram_similarity 0 half_ne swap
  have hu := hupp.parallelogram_similarity 0 half_ne swap
  rw [← map_eq_similarity,map_image_lowerFamily hpos.1 hcap,
    show 4*(k/4)=k by ring] at hl
  rw [← map_eq_similarity,map_image_upperFamily hpos.1 hcap,
    show 4*(k/4)=k by ring] at hu
  constructor
  · convert hl using 1
    rw [hdict]
    ring
  · convert hu using 1
    rw [hdict]
    ring

theorem cost_statement : CostStatement := by
  intro p ρ q hp hp' hadm
  have hs := Real.sq_sqrt (show (0:ℝ)≤51 by norm_num)
  have hn := Real.sqrt_nonneg (51:ℝ)
  have hp2 : p < 2 := by nlinarith
  have hcoef := (FlexibleSingular.flexible_singular p ρ q hp hp' hadm).1
  refine ⟨cost_asymptotic hp hp2.le hadm,?_⟩
  filter_upwards [totalCost_small hp hp2.le hadm hcoef,
    finite_families_eventually hp hp2 hadm] with k hsmall hfam
  exact ⟨hsmall,hfam⟩

theorem alternative_cost : AlternativeCostStatement := by
  intro p β hp hp' hβ hβp
  have hs := Real.sq_sqrt (show (0:ℝ)≤51 by norm_num)
  have hn := Real.sqrt_nonneg (51:ℝ)
  have hp2 : p < 2 := by nlinarith
  have hadm := SingularCutoff.edge_one_alternative_admissible hp2 hβ hβp
  have hm := cost_statement p (SingularCutoff.powerCutoff 4 β)
    (SingularCutoff.powerPadding 4 1 (5/2)) hp hp' hadm
  simpa only [SingularCutoff.powerCutoff,SingularCutoff.powerPadding,one_mul,
    show ∀ k : ℝ, 4*(k/4)=k from fun k => by ring] using hm

end CylinderCovering.SingularEdgeOneCover

end

end OAI
