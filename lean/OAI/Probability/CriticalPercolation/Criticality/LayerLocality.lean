import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.BlockLocalization
import OAI.Probability.CriticalPercolation.Criticality.ContractingDomains
import OAI.Probability.CriticalPercolation.Criticality.NestedLayerBlock
import OAI.Probability.CriticalPercolation.Criticality.UniformLocalContinuity

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma layer_weight_lower
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (R : ℕ) (C : ℝ) (_hC : 0<C)
    (hlow : ∀ T : ℝ, {z | G.modularRatio z o≤T/C}⊆G.safeBallDomain o T R)
    (T δ : ℝ) (hT : 0<T) (x : V) (hx : x∈G.safeBallDomain o T R)
    (z : V) (hz : z∉G.safeBallDomain o (δ*T) R) :
    δ/C<G.modularRatio z x := by
  have hzlow : δ*T/C<G.modularRatio z o := lt_of_not_ge (fun hh => hz (hlow (δ*T) hh))
  have hxup := G.safeBallDomain_subset o T R hx
  have hmul : (δ/C)*T<G.modularRatio z x*T := by
    calc
      _ = δ*T/C := by ring
      _ < G.modularRatio z o := hzlow
      _ = G.modularRatio z x*G.modularRatio x o := (G.modularRatio_cocycle hc hl z x o).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hxup (G.modularRatio_pos hc hl z x).le
  exact lt_of_mul_lt_mul_right hmul hT.le

lemma uniform_nestedLayer_locality (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (o : V) (R : ℕ) (δ : ℝ) (hδ : 0<δ) (M : ℕ) :
    ∃ B : ℕ, ∀ T : ℝ, 0<T → ∀ x∈G.safeBallDomain o T R,
      x∉G.safeBallDomain o (δ*T) R → ∀ N : ℕ,
      DependsOn (fun ω : Set E => ω∈G.boundedDomainFreshExitEvent
        (G.safeBallDomain o T R) (G.safeBallDomain o (δ*T) R)ᶜ x N M)
        (G.incidentEdges (G.vertexBall x B)) := by
  obtain ⟨C,hC,hlow⟩ := G.safeBallDomain_low_inclusion hc hl hq R
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hr : 0<δ/C := div_pos hδ hC0
  obtain ⟨B,hB⟩ := exists_nat_gt ((M:ℝ)/(δ/C))
  have hBM : (M:ℝ)<(δ/C)*((B:ℝ)+1) := by
    have hh := (div_lt_iff₀ hr).mp hB
    nlinarith
  have hBM' : (M:ℝ≥0∞)<ENNReal.ofReal (δ/C)*(B+1) := by
    rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_natCast,←ENNReal.ofReal_one,
      ←ENNReal.ofReal_add (Nat.cast_nonneg B) zero_le_one,←ENNReal.ofReal_mul hr.le]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hBM
  refine ⟨B,fun T hT x hx hx' N => ?_⟩
  apply G.dependsOn_boundedDomainFreshExit _ _ x hx' (ENNReal.ofReal (δ/C)) M B N _ hBM'
  intro z hz
  exact ENNReal.ofReal_le_ofReal (G.layer_weight_lower hc hl o R C hC0
    (fun T => hlow o T) T δ hT x hx z hz).le

theorem uniform_lower_nestedLayer_blocks
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬G.CombinatoriallyUnimodular) (o : V)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (hper : 0<G.law p G.percolates)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    ∃ R : ℕ, ∃ θ : ℝ, 0<θ ∧ ∃ M : ℕ, 1≤M ∧ ∀ a : ℝ, 0<a → ∀ N : ℕ,
      ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ δ<a ∧ ∃ q : unitInterval, 0<(q:ℝ) ∧ q<p ∧
      ∀ T : ℝ, 0<T → ∀ x∈G.safeBallDomain o T R, a*T≤G.modularRatio x o →
        θ<(G.law q).real (G.boundedDomainFreshExitEvent
          (G.safeBallDomain o T R) (G.safeBallDomain o (δ*T) R)ᶜ x N M) := by
  obtain ⟨R,θ,hθ,M,hM,hblock⟩ := G.uniform_nestedLayer_blocks hc hl hq hu o p hp hp1 hper hm
  refine ⟨R,θ/2,by positivity,M,hM,fun a ha N => ?_⟩
  obtain ⟨δ,hδ,hδ1,hδa,hgood⟩ := hblock a ha N
  obtain ⟨B,hB⟩ := G.uniform_nestedLayer_locality hc hl hq o R δ hδ M
  have hcontinuity := G.eventually_uniform_local_events hl hq p B (θ/2) (by positivity)
  have hpos : ∀ᶠ q : unitInterval in 𝓝 p, 0<(q:ℝ) :=
    continuous_subtype_val.continuousAt.eventually (lt_mem_nhds hp)
  have : NeBot (𝓝[<] p) := nhdsLT_neBot_of_exists_lt ⟨0,hp⟩
  obtain ⟨q,hqgood,hqpos,hqp⟩ := ((hcontinuity.filter_mono nhdsWithin_le_nhds).and
    ((hpos.filter_mono nhdsWithin_le_nhds).and
      (show ∀ᶠ q in 𝓝[<] p, q<p from self_mem_nhdsWithin))).exists
  refine ⟨δ,hδ,hδ1,hδa,q,hqpos,hqp,fun T hT x hx hband => ?_⟩
  have hx' : x∉G.safeBallDomain o (δ*T) R := by
    intro hh
    have hh' : G.modularRatio x o≤δ*T := G.safeBallDomain_subset o (δ*T) R hh
    nlinarith
  have hc' := hqgood x _ (hB T hT x hx hx' N)
  have hg := hgood T hT x hx hband
  rw [abs_lt] at hc'
  linarith [hc'.1]

end CriticalPercolation.BondGraph
end
end

end OAI
