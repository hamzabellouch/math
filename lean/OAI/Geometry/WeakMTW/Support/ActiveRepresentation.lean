import Mathlib
import OAI.Geometry.WeakMTW.Support.CollisionTangentCoordinates
import OAI.Geometry.WeakMTW.Support.ActiveGraphLimits
import OAI.Geometry.WeakMTW.Support.ConvexRepresentation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 abbrev ActiveIndex (n : ℕ) := Fin (Module.finrank ℝ (Model n)+1)

 structure ActiveRepresentation (y : ι → M) (h : ι → ℝ) (p : TangentBundle (model n) M) where
  a : ActiveIndex n → TangentSpace (model n) p.1
  θ : ActiveIndex n → ℝ
  active : ∀ i, a i ∈ activeVelocities y h p.1
  nonneg : ∀ i, 0 ≤ θ i
  sum_one : ∑ i, θ i = 1
  bary : ∑ i, θ i • a i = p.2

 omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
   (fun x : M => TangentSpace (model n) x)] [IsRiemannianManifold (model n) M]
   [CompactSpace M] in
 theorem activeRepresentation_exists (y : ι → M) (h : ι → ℝ)
    {p : TangentBundle (model n) M} (hp : p ∈ activeHullGraph y h) :
    Nonempty (ActiveRepresentation y h p) := by
  let : FiniteDimensional ℝ (TangentSpace (model n) p.1) :=
    VectorBundle.finiteDimensional ℝ (Model n) _ p.1
  obtain ⟨a,θ,ha,hθ,hs,hb⟩ := ConvexRepresentation.fixed_size hp
    (show Module.finrank ℝ (TangentSpace (model n) p.1)+1 ≤ Module.finrank ℝ (Model n)+1 by
      rw [VectorBundle.finrank_eq ℝ (Model n) (TangentSpace (model n)) p.1])
  exact ⟨⟨a,θ,ha,hθ,hs,hb⟩⟩

 theorem activeRepresentation_subseq (y : ι → M) (h : ι → ℝ)
    {p : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) (R : ∀ j, ActiveRepresentation y h (p j)) :
    ∃ R₀ : ActiveRepresentation y h p₀, ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      (∀ i, Tendsto (fun j => (R (ρ j)).θ i) atTop (𝓝 (R₀.θ i))) ∧
      (∀ i, Tendsto (fun j => (⟨(p (ρ j)).1,(R (ρ j)).a i⟩ : TangentBundle (model n) M))
        atTop (𝓝 ⟨p₀.1,R₀.a i⟩)) := by
  let := tangentBundle_firstCountable (n := n) (M := M)
  let D : Set ((ActiveIndex n → ℝ) × (ActiveIndex n → TangentBundle (model n) M)) :=
    {θ | (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1} ×ˢ {A | ∀ i, A i ∈ activeGraph y h}
  have hsimplex : IsCompact {θ : ActiveIndex n → ℝ | (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1} := by
    simpa only [Convexity.StdSimplex.range_toFun_comp_weights, Set.ofPred_forall,
      Set.ofPred_and] using
      (isCompact_range
        (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (ActiveIndex n)).continuous)
  have hD : IsCompact D := hsimplex.prod
    (isCompact_pi_infinite (fun _ : ActiveIndex n => activeGraph_compact y h))
  obtain ⟨⟨θ,A⟩,hmem,ρ,hρ,hlim⟩ := hD.tendsto_subseq (fun j =>
    show ((R j).θ,fun i => (⟨(p j).1,(R j).a i⟩ : TangentBundle (model n) M)) ∈ D from
      ⟨⟨(R j).nonneg,(R j).sum_one⟩,(R j).active⟩)
  have hθ (i : ActiveIndex n) : Tendsto (fun j => (R (ρ j)).θ i) atTop (𝓝 (θ i)) :=
    ((continuous_apply i).comp continuous_fst).continuousAt.tendsto.comp hlim
  have hA (i : ActiveIndex n) : Tendsto
      (fun j => (⟨(p (ρ j)).1,(R (ρ j)).a i⟩ : TangentBundle (model n) M)) atTop (𝓝 (A i)) :=
    ((continuous_apply i).comp continuous_snd).continuousAt.tendsto.comp hlim
  have hbcont : Continuous (fun q : TangentBundle (model n) M => q.1) :=
    (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous
  have hpbase : Tendsto (fun j => (p (ρ j)).1) atTop (𝓝 p₀.1) :=
    hbcont.continuousAt.tendsto.comp (hp.comp hρ.tendsto_atTop)
  have hbase (i : ActiveIndex n) : (A i).1 = p₀.1 := by
    have hlimbase := (hbcont.tendsto (A i)).comp (hA i)
    change Tendsto (fun j => (p (ρ j)).1) atTop (𝓝 (A i).1) at hlimbase
    exact tendsto_nhds_unique hlimbase hpbase
  have hap (i : ActiveIndex n) : ∃ v : TangentSpace (model n) p₀.1,
      A i = (⟨p₀.1,v⟩ : TangentBundle (model n) M) := by
    rcases he : A i with ⟨x,v⟩
    have hx : x = p₀.1 := by simpa only [he] using hbase i
    subst x
    exact ⟨v,rfl⟩
  choose a haeq using hap
  have ha (i : ActiveIndex n) : a i ∈ activeVelocities y h p₀.1 := by
    have hh : A i ∈ activeGraph y h := hmem.2 i
    rw [haeq i] at hh
    exact hh
  have hA' (i : ActiveIndex n) : Tendsto
      (fun j => (⟨(p (ρ j)).1,(R (ρ j)).a i⟩ : TangentBundle (model n) M))
      atTop (𝓝 ⟨p₀.1,a i⟩) := by rw [← haeq i]; exact hA i
  have hbary : ∑ i, θ i • a i = p₀.2 := by
    let c := stateChart (E := Model n) p₀.1
    have hpS : p₀ ∈ c.source := (stateChart_source p₀.1 p₀).mpr (mem_chart_source (Model n) p₀.1)
    have hcP := (c.continuousAt hpS).tendsto.comp (hp.comp hρ.tendsto_atTop)
    have hcA (i : ActiveIndex n) : Tendsto
        (fun j => (c (⟨(p (ρ j)).1,(R (ρ j)).a i⟩ : TangentBundle (model n) M)).2)
        atTop (𝓝 ((c (⟨p₀.1,a i⟩ : TangentBundle (model n) M)).2)) := by
      have hAiS : (⟨p₀.1,a i⟩ : TangentBundle (model n) M) ∈ c.source :=
        (stateChart_source p₀.1 _).mpr (mem_chart_source (Model n) p₀.1)
      have htmp := (c.continuousAt hAiS).tendsto.comp (hA' i)
      exact continuous_snd.continuousAt.tendsto.comp htmp
    have hsum := tendsto_finsetSum Finset.univ (fun i _ => (hθ i).smul (hcA i))
    have hpSrc : ∀ᶠ j in atTop, p (ρ j) ∈ c.source :=
      (hp.comp hρ.tendsto_atTop) (c.open_source.mem_nhds hpS)
    have hsum' : Tendsto (fun j => ∑ i, (R (ρ j)).θ i •
        (c (⟨(p (ρ j)).1,(R (ρ j)).a i⟩ : TangentBundle (model n) M)).2)
        atTop (𝓝 ((c p₀).2)) := by
      apply (continuous_snd.continuousAt.tendsto.comp hcP).congr'
      filter_upwards [hpSrc] with j hj
      rw [← stateChart_bary p₀.1 (p (ρ j)).1 ((stateChart_source p₀.1 _).mp hj), (R (ρ j)).bary]
      rfl
    have heq := tendsto_nhds_unique hsum hsum'
    apply (tangentCoordinateEquiv p₀.1 p₀.1 (mem_chart_source (Model n) p₀.1)).injective
    simpa only [map_sum,map_smul,tangentCoordinateEquiv_apply] using heq
  exact ⟨⟨a,θ,ha,hmem.1.1,hmem.1.2,hbary⟩,ρ,hρ,hθ,hA'⟩

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
