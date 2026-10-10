import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.ContractingDomains
import OAI.Probability.CriticalPercolation.Criticality.MinimalPair
import OAI.Probability.CriticalPercolation.Modular.LightSliceFrontier

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularRatio_ball_weight (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (R : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ o x y, y∈G.vertexBall x R →
      G.modularRatio x o≤C*G.modularRatio y o := by
  obtain ⟨C,hC,hbound⟩ := G.modularRatio_ball_upper hc hl hq R
  refine ⟨C,hC,fun o x y hy => ?_⟩
  rw [←G.modularRatio_cocycle hc hl x y o]
  exact mul_le_mul_of_nonneg_right (hbound y x (G.vertexBall_comm.mp hy))
    (G.modularRatio_pos hc hl y o).le

lemma walk_support_mem_start_ball {x y : V} (w : G.fullGraph.Walk x y)
    {L : ℕ} (hw : w.length≤L) {z : V} (hz : z∈w.support) : z∈G.vertexBall x L :=
  G.vertexBall_mono x ((w.length_takeUntil_le_length hz).trans hw)
    (G.walk_mem_vertexBall (w.takeUntil z hz))

lemma finite_cluster_outside_safe
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (o : V) (T : ℝ) (hT : 0<T) (R : ℕ) (x : V)
    (hx : x∉G.safeBallDomain o T R) (ω : Set E)
    (hm : G.modularMass x (G.cluster ω x)≠∞) :
    (G.cluster (ω∩G.inducedEdges (G.safeBallDomain o T R)ᶜ) x).Finite := by
  obtain ⟨C,hC,hlow⟩ := G.safeBallDomain_low_inclusion hc hl hq R
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hS : (G.safeBallDomain o T R)ᶜ⊆G.modularUpperSlice o (T/C) := by
    intro z hz
    change T/C≤G.modularRatio z o
    exact (lt_of_not_ge (fun h : G.modularRatio z o≤T/C => hz (hlow o T h))).le
  have hmass : G.modularMass o (G.cluster ω x)≠∞ :=
    mt (G.modularMass_eq_top_change_base hc hl o x _).mp hm
  apply (G.finite_lightUpperSlice o x (T/C) (div_pos hT hC0) ω hmass).subset
  intro z hz
  exact ⟨G.cluster_mono Set.inter_subset_left x hz,
    hS (G.cluster_induced_subset ω _ hx hz)⟩

lemma exists_layer_gap (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (o : V) (a : ℝ) (ha : 0<a) (L H R : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ δ<a ∧ ∀ (T : ℝ), 0<T → ∀ (x : V),
      a*T≤G.modularRatio x o →
      (∀ z∈G.vertexBall x L, z∉G.safeBallDomain o (δ*T) R) ∧
      (∀ y∈G.vertexBall x L, G.vertexBall y H⊆(G.safeBallDomain o (δ*T) R)ᶜ) := by
  obtain ⟨A,hA,hboundA⟩ := G.modularRatio_ball_weight hc hl hq L
  obtain ⟨B,hB,hboundB⟩ := G.modularRatio_ball_weight hc hl hq H
  have hA0 : 0<A := lt_of_lt_of_le zero_lt_one hA
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  let δ : ℝ := min (1/2) (a/(2*(A*B)))
  have hδ : 0<δ := lt_min (by norm_num) (div_pos ha (by positivity))
  have hδ1 : δ<1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδAB : δ*(A*B)≤a/2 := by
    have hh := (le_div_iff₀ (show 0<2*(A*B) by positivity)).mp (min_le_right (1/2) (a/(2*(A*B))))
    change δ*(2*(A*B))≤a at hh
    nlinarith
  have hδa : δ<a := by
    have hδA : δ≤δ*(A*B) := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
    linarith
  refine ⟨δ,hδ,hδ1,hδa,fun T hT x hx => ?_⟩
  have hlow (z : V) (hz : z∈G.vertexBall x L) :
      δ*T<G.modularRatio z o := by
    have hh := hboundA o x z hz
    have hz0 := G.modularRatio_pos hc hl z o
    have hAδ : δ*A≤a/2 := by nlinarith [mul_nonneg hδ.le hA0.le]
    have ht := mul_le_mul_of_nonneg_right hAδ hT.le
    nlinarith
  refine ⟨fun z hz hs => (not_le_of_gt (hlow z hz)) (G.safeBallDomain_subset o (δ*T) R hs),?_⟩
  intro y hy z hz hs
  have h1 := hboundA o x y hy
  have h2 := hboundB o y z hz
  have h3 := mul_le_mul_of_nonneg_left h2 hA0.le
  have ht := mul_le_mul_of_nonneg_right hδAB hT.le
  have hzlow : δ*T<G.modularRatio z o := by
    by_contra hh
    have hzle : G.modularRatio z o≤δ*T := le_of_not_gt hh
    have hu := mul_le_mul_of_nonneg_left hzle (mul_pos hA0 hB0).le
    nlinarith
  exact (not_le_of_gt hzlow) (G.safeBallDomain_subset o (δ*T) R hs)

end CriticalPercolation.BondGraph
end
end

end OAI
