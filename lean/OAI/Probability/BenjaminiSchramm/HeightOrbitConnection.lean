import OAI.Probability.BenjaminiSchramm.UniformHeightAscent

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem height_uniform_orbit_connection_abs [Fintype G.VertexOrbit]
    (hc : G.fullGraph.Connected) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x) :
    ∃ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ x (j : G.VertexOrbit), ∃ y,
      ∃ w : G.fullGraph.Walk x y, G.vertexOrbit y = j ∧ w.length ≤ N ∧
        ∀ v ∈ w.support, |G.orbitAdjustedHeight a x v| ≤ D := by
  let w : (i j : G.VertexOrbit) → G.fullGraph.Walk i.out j.out := fun i j => (hc i.out j.out).some
  let N : ℕ := ∑ i : G.VertexOrbit, ∑ j : G.VertexOrbit, (w i j).length
  let b : G.VertexOrbit → G.VertexOrbit → ℝ := fun i j =>
    ∑ v ∈ (w i j).support.toFinset, |G.orbitAdjustedHeight a i.out v|
  let D : ℝ := ∑ i : G.VertexOrbit, ∑ j : G.VertexOrbit, b i j
  have hb (i j : G.VertexOrbit) : 0 ≤ b i j := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hb i j
  have hlen (i j : G.VertexOrbit) : (w i j).length ≤ N :=
    (Finset.single_le_sum (f := fun k => (w i k).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k => ∑ j, (w k j).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hd (i j : G.VertexOrbit) (v : V) (hv : v ∈ (w i j).support) :
      |G.orbitAdjustedHeight a i.out v| ≤ D :=
    (Finset.single_le_sum (fun _ _ => abs_nonneg _) (List.mem_toFinset.mpr hv)).trans
      ((Finset.single_le_sum (fun j _ => hb i j) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hb i j) (Finset.mem_univ i)))
  refine ⟨N,D,hD,fun x j => ?_⟩
  let i := G.vertexOrbit x
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut x
  let f : G.fullGraph →g G.fullGraph :=
    ⟨φ.vertex,fun {_ _} h => (Aut.fullGraph_adj G φ _ _).mpr h⟩
  refine ⟨φ.vertex j.out,((w i j).map f).copy hφ rfl,?_,?_,?_⟩
  · rw [G.vertexOrbit_aut]
    exact j.out_eq'
  · simpa only [SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map] using hlen i j
  · intro v hv
    simp only [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map,List.mem_map] at hv
    obtain ⟨z,hz,rfl⟩ := hv
    change |G.orbitAdjustedHeight a x (φ.vertex z)| ≤ D
    rw [← hφ,G.orbitAdjustedHeight_aut a ha]
    exact hd i j z hz

theorem height_uniform_orbit_connection [Fintype G.VertexOrbit]
    (hc : G.fullGraph.Connected) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x) :
    ∃ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ x (j : G.VertexOrbit), ∃ y,
      ∃ w : G.fullGraph.Walk x y, G.vertexOrbit y = j ∧ w.length ≤ N ∧
        ∀ v ∈ w.support, -D ≤ G.orbitAdjustedHeight a x v := by
  obtain ⟨N,D,hD,h⟩ := G.height_uniform_orbit_connection_abs hc a ha
  refine ⟨N,D,hD,fun x j => ?_⟩
  obtain ⟨y,w,hy,hw,hh⟩ := h x j
  exact ⟨y,w,hy,hw,fun v hv => (abs_le.mp (hh v hv)).1⟩

theorem stationaryOrbitHeight_orbit_above [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ)
    (hu : ¬ G.CombinatoriallyUnimodular) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r → ∀ x (j : G.VertexOrbit),
      ∃ y, ∃ w : G.fullGraph.Walk x y, G.vertexOrbit y = j ∧
        (w.length : ℝ) ≤ A*r+B ∧
        (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v) ∧
        r ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y := by
  obtain ⟨ε,hε,L,hstep⟩ := G.stationaryOrbitHeight_uniform_ascent hc hl hq μ hμ hstat hu
  let a := G.stationaryOrbitWeight μ
  obtain ⟨N,D,hD,hconn⟩ := G.height_uniform_orbit_connection hc a (G.stationaryOrbitWeight_aut μ)
  let A : ℝ := (L : ℝ)/ε+1
  let B : ℝ := (D/ε+1)*L+N
  refine ⟨A,B,by dsimp [A]; positivity,by dsimp [B]; positivity,fun r hr x j => ?_⟩
  let n : ℕ := ⌈(r+D)/ε⌉₊
  have hn : r+D ≤ (n : ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil ((r+D)/ε))
  have hn' : (n : ℝ) ≤ (r+D)/ε+1 :=
    (Nat.ceil_lt_add_one (div_nonneg (add_nonneg hr hD) hε.le)).le
  obtain ⟨y,w,hwlen,hw,hwy⟩ := G.height_ascent_iterate hc hl a ε hε.le L hstep n x
  obtain ⟨z,q,hqorb,hqlen,hq⟩ := hconn y j
  refine ⟨z,w.append q,hqorb,?_,?_,?_⟩
  · rw [SimpleGraph.Walk.length_append,Nat.cast_add]
    have hwl : (w.length : ℝ) ≤ (n : ℝ)*L := by exact_mod_cast hwlen
    have hql : (q.length : ℝ) ≤ N := by exact_mod_cast hqlen
    have hm := mul_le_mul_of_nonneg_right hn' (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    have he : (((r+D)/ε+1)*L+(N : ℝ)) = (L:ℝ)/ε*r+B := by dsimp [B]; ring
    calc
      _ ≤ (n : ℝ)*L+(N : ℝ) := add_le_add hwl hql
      _ ≤ ((r+D)/ε+1)*L+(N : ℝ) := add_le_add hm le_rfl
      _ = (L : ℝ)/ε*r+B := he
      _ ≤ A*r+B := by dsimp [A]; nlinarith
  · intro v hv
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
    · exact hw v hv
    · rw [G.orbitAdjustedHeight_change_base hc hl a x y v]
      have hv' := hq v hv
      linarith
  · rw [G.orbitAdjustedHeight_change_base hc hl a x y z]
    have hz := hq z q.end_mem_support
    linarith

end CriticalPercolation.BondGraph

end

end OAI
