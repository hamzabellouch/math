import OAI.Probability.BenjaminiSchramm.UniformHeightDescent

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace Percolation.BenjaminiSchramm

lemma walk_height_support_bound {V : Type*} {H : SimpleGraph V}
    (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hj : ∀ {v w}, H.Adj v w → |f w-f v| ≤ R)
    {x y : V} (p : H.Walk x y) :
    ∀ v ∈ p.support, |f v-f x| ≤ (p.length : ℝ)*R := by
  induction p with
  | @nil u =>
    intro v hv
    have he : v=u := List.mem_singleton.mp hv
    simp only [he,sub_self,abs_zero,SimpleGraph.Walk.length_nil,Nat.cast_zero,zero_mul,le_refl]
  | @cons x z y hxy p ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · simp only [sub_self,abs_zero,SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
      positivity
    · calc
        _ = |(f v-f z)+(f z-f x)| := by congr 1; ring
        _ ≤ |f v-f z|+|f z-f x| := abs_add_le _ _
        _ ≤ (p.length : ℝ)*R+R := add_le_add (ih v hv) (hj hxy)
        _ = _ := by rw [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]; ring

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_bounded_orbit_below [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ N : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ x (j : G.VertexOrbit), ∃ y,
      ∃ w : G.fullGraph.Walk x y, G.vertexOrbit y=j ∧ w.length ≤ N ∧
        (∀ v ∈ w.support, -M ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0) ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤ -R := by
  obtain ⟨A,B,hA,hB,hpath⟩ := G.stationaryOrbitHeight_orbit_below hc hl hq μ hμ hstat hu
  let N : ℕ := ⌈A*R+B⌉₊
  let M : ℝ := (N : ℝ)*R+R
  refine ⟨N,M,by dsimp [M]; positivity,fun x j => ?_⟩
  obtain ⟨y,w,hy,hlen,hw,hend⟩ := hpath R hR.le x j
  have hlenN : w.length ≤ N := by
    exact_mod_cast hlen.trans (Nat.le_ceil (A*R+B))
  let a := G.stationaryOrbitWeight μ
  let f := G.orbitAdjustedHeight a x
  have hj {v v' : V} (hv : G.fullGraph.Adj v v') : |f v'-f v| ≤ R := by
    obtain ⟨⟨e,_he,heq⟩,_hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hv
    have hh := hjump e v v' (by rw [heq]; simp) (by rw [heq]; simp)
    have he : f v'-f v=G.orbitAdjustedHeight a v v' := by
      dsimp [f]
      rw [G.orbitAdjustedHeight_change_base hc hl _ x v v',add_sub_cancel_left]
    rwa [he]
  refine ⟨y,w,hy,hlenN,fun v hv => ⟨?_,hw v hv⟩,hend⟩
  have hh := walk_height_support_bound f R hR.le hj w v hv
  have hf : f x=0 := G.orbitAdjustedHeight_self a x
  rw [hf,sub_zero] at hh
  have hN : (w.length : ℝ)*R ≤ (N : ℝ)*R :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlenN) hR.le
  have hv' := (abs_le.mp hh).1
  change -M ≤ f v
  dsimp [M]
  linarith

end CriticalPercolation.BondGraph

end

end OAI
