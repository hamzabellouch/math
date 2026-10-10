import OAI.Probability.BenjaminiSchramm.CrossingExponent

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem adjustedHalfspaceHit_walk_lower [Countable E] (a : V → ℝ) (p : unitInterval)
    {x y : V} (w : G.fullGraph.Walk x y) (t : ℝ)
    (hw : ∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight a x v)
    (hy : t ≤ G.orbitAdjustedHeight a x y) :
    (p : ℝ)^w.length ≤ (G.law p).real (G.adjustedHalfspaceHit a x 0 t) := by
  have hg : G.fullGraph = Percolation.openSimpleGraph G.ends Set.univ :=
    criticalModel_openGraph G.ends Set.univ
  let f : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by simpa only [← hg,id_eq] using h⟩
  obtain ⟨s,hs,hconn⟩ := walk_finite_open_restriction G.ends (w.map f)
    {v | 0 ≤ G.orbitAdjustedHeight a x v} (by
      intro v hv
      rw [SimpleGraph.Walk.support_map] at hv
      change v ∈ w.support.map id at hv
      exact hw v (by simpa only [List.map_id_fun,id_eq] using hv))
  have hslen : s.card ≤ w.length := by simpa only [SimpleGraph.Walk.length_map] using hs
  have hsub : {ω : Set E | (s : Set E) ⊆ ω} ⊆ G.adjustedHalfspaceHit a x 0 t :=
    fun ω hω => ⟨y,hy,hconn ω hω⟩
  calc
    _ ≤ (p : ℝ)^s.card := pow_le_pow_of_le_one p.2.1 p.2.2 hslen
    _ = (G.law p).real {ω : Set E | (s : Set E) ⊆ ω} :=
      (Percolation.finite_open_probability p s).symm
    _ ≤ _ := measureReal_mono hsub

theorem infimalAdjustedCrossing_finite_energy [Fintype G.VertexOrbit] [Nontrivial V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ = μ) (hu : ¬ G.CombinatoriallyUnimodular)
    (p : unitInterval) (hp : 0 < (p : ℝ)) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      (p : ℝ)^(A*t+B) ≤ (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p t).toReal := by
  obtain ⟨A,B,hA,hB,hpath⟩ := G.stationaryOrbitHeight_orbit_above hc hl hq μ hμ hstat hu
  refine ⟨A,B,hA,hB,fun t ht => ?_⟩
  have hroot (x : V) : (p : ℝ)^(A*t+B) ≤
      (G.law p).real (G.adjustedHalfspaceHit (G.stationaryOrbitWeight μ) x 0 t) := by
    obtain ⟨y,w,_horb,hlen,hw,hy⟩ := hpath t ht x (G.vertexOrbit x)
    have hc := G.adjustedHalfspaceHit_walk_lower (G.stationaryOrbitWeight μ) p w t hw hy
    have hcoeff : (p : ℝ)^(A*t+B) ≤ (p : ℝ)^w.length := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_ge hp p.2.2 hlen
    exact hcoeff.trans hc
  have he : ENNReal.ofReal ((p : ℝ)^(A*t+B)) ≤
      G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p t :=
    le_iInf fun x => ENNReal.ofReal_le_of_le_toReal (hroot x)
  have hf := ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top (G.infimalAdjustedCrossing_le_one _ p t)) he
  rwa [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hp _).le] at hf

theorem normalized_crossing_exponent [Fintype G.VertexOrbit] [Nontrivial V]
    [Encodable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ = μ) (hu : ¬ G.CombinatoriallyUnimodular)
    (p : unitInterval) (hp : 0 < (p : ℝ)) :
    ∃ α : ℝ, 0 ≤ α ∧
      (∀ n : ℕ, (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p n).toReal ≤ Real.exp (-α*n)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
        c*Real.exp (-(α+ε)*n) ≤ (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p n).toReal) ∧
      Tendsto (fun n : ℕ => -Real.log
        (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p n).toReal/n) atTop (𝓝 α) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,_hA,_hB,hbound⟩ := G.infimalAdjustedCrossing_finite_energy hc hl hq μ hμ hstat hu p hp
  obtain ⟨m,M,hm,ha⟩ := G.stationaryOrbitWeight_uniform_bounds hc hl μ hμ
  have hne (t : ℝ) : G.infimalAdjustedCrossing a p t ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (G.infimalAdjustedCrossing_le_one a p t)
  apply positive_crossing_exponent (fun n : ℕ => (G.infimalAdjustedCrossing a p n).toReal)
  · intro n
    exact (Real.rpow_pos_of_pos hp _).trans_le (hbound n (Nat.cast_nonneg n))
  · intro n
    exact (ENNReal.toReal_mono ENNReal.one_ne_top (G.infimalAdjustedCrossing_le_one a p n)).trans_eq
      ENNReal.toReal_one
  · simp
  · intro n k
    have hh := ENNReal.toReal_mono (hne (n+k))
      (G.infimalAdjustedCrossing_supermultiplicative hc hl hq a m M hm ha p
        (Nat.cast_nonneg n) (Nat.cast_nonneg k))
    simpa only [ENNReal.toReal_mul,Nat.cast_add] using hh

end CriticalPercolation.BondGraph

end

end OAI
