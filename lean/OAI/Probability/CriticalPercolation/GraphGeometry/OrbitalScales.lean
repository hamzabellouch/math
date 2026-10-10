import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitalAction
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitalPower

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma dense_set_infinite [Infinite V] (hl : G.LocallyFinite) {O : Set V} {C : ℕ}
    (hdense : ∀ x : V, ∃ u : O, u.val∈G.vertexBall x C) : O.Infinite := by
  intro hO
  have hh : (⋃ u∈O, G.vertexBall u C).Finite :=
    hO.biUnion (fun u _ => G.vertexBall_finite hl u C)
  apply Set.infinite_univ.not_finite (hh.subset ?_)
  intro v _
  obtain ⟨u,hu⟩ := hdense v
  exact Set.mem_iUnion₂.mpr ⟨u.val,u.property,G.vertexBall_comm.mp hu⟩

lemma polynomial_scale_arithmetic (C L d N R : ℕ) (hL : 0<L)
    (hR : C+L*(max N ((C+2*L)^d)+1)≤R) :
    let n := (R-C)/L
    N≤n ∧ C+L*n≤R ∧ R^d≤n^(d+1) := by
  dsimp
  let n := (R-C)/L
  change N≤n ∧ C+L*n≤R ∧ R^d≤n^(d+1)
  have hC : C≤R := by omega
  have hsub : R-C+C=R := Nat.sub_add_cancel hC
  have hN : max N ((C+2*L)^d)+1≤n := by
    apply (Nat.le_div_iff_mul_le hL).mpr
    nlinarith
  have hn : 1≤n := by omega
  have hmul : L*n≤R-C := by
    dsimp [n]
    exact Nat.mul_div_le (R-C) L
  have hmod : R-C<L*n+L := by
    have he := Nat.div_add_mod (R-C) L
    have ht := Nat.mod_lt (R-C) hL
    dsimp [n]
    nlinarith
  have hcn : C+L≤(C+L)*n := by nlinarith [Nat.mul_le_mul_left (C+L) hn]
  have hupper : R≤(C+2*L)*n := by nlinarith
  refine ⟨by omega,by omega,?_⟩
  calc
    R^d ≤ ((C+2*L)*n)^d := Nat.pow_le_pow_left hupper d
    _ = (C+2*L)^d*n^d := Nat.mul_pow _ _ _
    _ ≤ n*n^d := Nat.mul_le_mul_right _ (by omega)
    _ = n^(d+1) := by rw [pow_succ,Nat.mul_comm]

theorem orbital_power_polynomial_scales (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) :
    ∃ C : ℕ, (G.orbitPower o (2*C+1)).Connected ∧
      (∀ x, ∃ u : MulAction.orbit G.Aut o, u.val∈G.vertexBall x C) ∧
      (∀ N : ℕ, ∃ n≥N, ∀ u : MulAction.orbit G.Aut o,
        {v | ∃ p : (G.orbitPower o (2*C+1)).Walk u v, p.length≤n}.ncard≤n^(d+1)) := by
  obtain ⟨C,hC,hdense⟩ := G.orbitPower_connected hc hq o
  refine ⟨C,hC,hdense,?_⟩
  intro N
  let L := 2*C+1
  obtain ⟨R,hR,x,hx⟩ := hpoly (C+L*(max N ((C+2*L)^d)+1))
  obtain ⟨u,hu⟩ := hdense x
  have hh := polynomial_scale_arithmetic C L d N R (by dsimp [L]; omega) hR
  dsimp only at hh
  refine ⟨(R-C)/L,hh.1,?_⟩
  intro v
  rw [G.orbitPower_ball_ncard o L ((R-C)/L) v u]
  exact (G.powerOn_ball_card_le hl x u hu hh.2.1).trans (hx.trans hh.2.2)

end CriticalPercolation.BondGraph
end
end
end

end OAI
