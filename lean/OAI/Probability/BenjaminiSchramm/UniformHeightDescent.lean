import OAI.Probability.BenjaminiSchramm.HarmonicHeightDescent
import OAI.Probability.BenjaminiSchramm.HeightOrbitConnection

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_uniform_descent [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ)
    (hu : ¬ G.CombinatoriallyUnimodular) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L : ℕ, ∀ x, ∃ y, ∃ w : G.fullGraph.Walk x y,
      w.length ≤ L ∧
      (∀ v ∈ w.support, G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0) ∧
      G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤ -ε := by
  let : Nonempty G.VertexOrbit := ⟨G.vertexOrbit (Classical.arbitrary V)⟩
  choose y w hw hr using fun i : G.VertexOrbit =>
    G.stationaryOrbitHeight_descent hc hl hq μ hμ hstat hu i.out
  let a := G.stationaryOrbitWeight μ
  let fall : G.VertexOrbit → ℝ := fun i => -G.orbitAdjustedHeight a i.out (y i)
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ fall Finset.univ_nonempty
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ
    (fun k : G.VertexOrbit => (w k).length) Finset.univ_nonempty
  refine ⟨fall i,neg_pos.mpr (hr i),(w j).length,fun x => ?_⟩
  let k := G.vertexOrbit x
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut x
  let f : G.fullGraph →g G.fullGraph :=
    ⟨φ.vertex,fun {_ _} h => (Aut.fullGraph_adj G φ _ _).mpr h⟩
  refine ⟨φ.vertex (y k),((w k).map f).copy hφ rfl,?_,?_,?_⟩
  · simpa only [SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map] using
      hj k (Finset.mem_univ _)
  · intro v hv
    simp only [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map,List.mem_map] at hv
    obtain ⟨z,hz,rfl⟩ := hv
    change G.orbitAdjustedHeight a x (φ.vertex z) ≤ 0
    rw [← hφ,G.orbitAdjustedHeight_aut a (G.stationaryOrbitWeight_aut μ)]
    exact hw k z hz
  · change G.orbitAdjustedHeight a x (φ.vertex (y k)) ≤ -fall i
    rw [← hφ,G.orbitAdjustedHeight_aut a (G.stationaryOrbitWeight_aut μ)]
    have hh := hi k (Finset.mem_univ _)
    dsimp [fall] at hh ⊢
    linarith

lemma height_descent_iterate (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (L : ℕ)
    (hstep : ∀ x, ∃ y, ∃ w : G.fullGraph.Walk x y, w.length ≤ L ∧
      (∀ v ∈ w.support, G.orbitAdjustedHeight a x v ≤ 0) ∧ G.orbitAdjustedHeight a x y ≤ -ε)
    (n : ℕ) (x : V) :
    ∃ y, ∃ w : G.fullGraph.Walk x y, w.length ≤ n*L ∧
      (∀ v ∈ w.support, G.orbitAdjustedHeight a x v ≤ 0) ∧
      G.orbitAdjustedHeight a x y ≤ -(n*ε) := by
  induction n with
  | zero =>
    refine ⟨x,.nil,by simp,?_,by simp⟩
    intro v hv
    have he : v = x := List.mem_singleton.mp hv
    rw [he,G.orbitAdjustedHeight_self]
  | succ n ih =>
    obtain ⟨y,w,hlen,hw,hr⟩ := ih
    obtain ⟨z,q,hqlen,hq,hqr⟩ := hstep y
    refine ⟨z,w.append q,?_,?_,?_⟩
    · rw [SimpleGraph.Walk.length_append]
      exact (Nat.add_le_add hlen hqlen).trans_eq (Nat.succ_mul n L).symm
    · intro v hv
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
      · exact hw v hv
      · rw [G.orbitAdjustedHeight_change_base hc hl a x y v]
        exact add_nonpos (hr.trans (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg n) hε))) (hq v hv)
    · rw [G.orbitAdjustedHeight_change_base hc hl a x y z]
      push_cast
      nlinarith

theorem stationaryOrbitHeight_orbit_below [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ)
    (hu : ¬ G.CombinatoriallyUnimodular) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r → ∀ x (j : G.VertexOrbit),
      ∃ y, ∃ w : G.fullGraph.Walk x y, G.vertexOrbit y = j ∧
        (w.length : ℝ) ≤ A*r+B ∧
        (∀ v ∈ w.support, G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0) ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤ -r := by
  obtain ⟨ε,hε,L,hstep⟩ := G.stationaryOrbitHeight_uniform_descent hc hl hq μ hμ hstat hu
  let a := G.stationaryOrbitWeight μ
  obtain ⟨N,D,hD,hconn⟩ := G.height_uniform_orbit_connection_abs hc a (G.stationaryOrbitWeight_aut μ)
  let A : ℝ := (L : ℝ)/ε+1
  let B : ℝ := (D/ε+1)*L+N
  refine ⟨A,B,by dsimp [A]; positivity,by dsimp [B]; positivity,fun r hr x j => ?_⟩
  let n : ℕ := ⌈(r+D)/ε⌉₊
  have hn : r+D ≤ (n : ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil ((r+D)/ε))
  have hn' : (n : ℝ) ≤ (r+D)/ε+1 :=
    (Nat.ceil_lt_add_one (div_nonneg (add_nonneg hr hD) hε.le)).le
  obtain ⟨y,w,hwlen,hw,hwy⟩ := G.height_descent_iterate hc hl a ε hε.le L hstep n x
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
      have hv' := (abs_le.mp (hq v hv)).2
      linarith
  · rw [G.orbitAdjustedHeight_change_base hc hl a x y z]
    have hz := (abs_le.mp (hq z q.end_mem_support)).2
    linarith

end CriticalPercolation.BondGraph

end

end OAI
