import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.MainSparseBoundary
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitalFiniteGeneration
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitalPacking
import OAI.Probability.CriticalPercolation.GraphTopology.OrbitalNeighborhoods

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def subgroupDisplacementBall (Λ : Subgroup G.Aut) (o : V) (r : ℕ) : Set Λ :=
  Λ.subtype ⁻¹' G.displacementBall o r

lemma subgroupDisplacementBall_cover (hl : G.LocallyFinite) (o : V) (r K : ℕ)
    (Λ : Subgroup G.Aut) (horbit : MulAction.orbit Λ o=MulAction.orbit G.Aut o)
    (hd : (G.orbitBall o (5*r)).ncard≤K*(G.orbitBall o r).ncard) :
    CovBySMul Λ (K : ℝ) (G.subgroupDisplacementBall Λ o (4*r))
      (G.subgroupDisplacementBall Λ o (2*r)) := by
  obtain ⟨F,hFo,hFK,hcover⟩ := G.orbitBall_packing hl o r K hd
  have hex : ∀ v : F, ∃ φ : Λ, φ • o=v.val := by
    intro v
    rw [←MulAction.mem_orbit_iff,horbit]
    exact (hFo v.property).1
  choose φ hφ using hex
  let H := Finset.univ.image φ
  have hH : H.card≤K := (Finset.card_image_le).trans (by simpa using hFK)
  refine ⟨H,by exact_mod_cast hH,?_⟩
  intro ψ hψ
  have hu : ψ.val • o∈G.orbitBall o (4*r) := ⟨MulAction.mem_orbit _ _,hψ⟩
  obtain ⟨v,hv,huv⟩ := hcover (ψ.val • o) hu
  let c := φ ⟨v,hv⟩
  have hc : c∈H := Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩
  have hco : c.val • o=v := hφ ⟨v,hv⟩
  have hrem : c⁻¹*ψ∈G.subgroupDisplacementBall Λ o (2*r) := by
    change (c.val⁻¹*ψ.val) • o∈G.vertexBall o (2*r)
    apply (Aut.vertexBall_mem G c.val o ((c.val⁻¹*ψ.val) • o) (2*r)).mp
    change c.val • ((c.val⁻¹*ψ.val) • o)∈G.vertexBall (c.val • o) (2*r)
    rw [←mul_smul,mul_inv_cancel_left,hco]
    exact huv
  change ψ∈(H : Set Λ)*G.subgroupDisplacementBall Λ o (2*r)
  exact Set.mem_mul.mpr ⟨c,hc,c⁻¹*ψ,hrem,by simp⟩

lemma subgroupDisplacementBall_approximate (hl : G.LocallyFinite) (o : V) (r K : ℕ)
    (Λ : Subgroup G.Aut) (horbit : MulAction.orbit Λ o=MulAction.orbit G.Aut o)
    (hd : (G.orbitBall o (5*r)).ncard≤K*(G.orbitBall o r).ncard) :
    IsApproximateSubgroup (K : ℝ) (G.subgroupDisplacementBall Λ o (2*r)) where
  one_mem := G.one_mem_displacementBall o _
  inv_eq_self := by
    ext φ
    change φ.val⁻¹∈G.displacementBall o (2*r) ↔ φ.val∈G.displacementBall o (2*r)
    exact G.inv_mem_displacementBall
  sq_covBySMul := by
    apply (G.subgroupDisplacementBall_cover hl o r K Λ horbit hd).subset_left
    rw [pow_two]
    rintro ψ ⟨φ,hφ,η,hη,rfl⟩
    change φ.val*η.val∈G.displacementBall o (4*r)
    have hh := G.displacementBall_mul_subset o (2*r) (2*r) (Set.mem_mul.mpr ⟨φ.val,hφ,η.val,hη,rfl⟩)
    simpa only [show 2*r+2*r=4*r by omega] using hh

theorem sparse_polynomial_finitelyGenerated_model (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) :
    ∃ Λ : Subgroup G.Aut, Group.FG Λ ∧
      MulAction.orbit Λ o=MulAction.orbit G.Aut o ∧
      (∃ S : Set V, S.Finite ∧ ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) ∧
      ∀ R : ℕ, ∃ n≥R, IsApproximateSubgroup (5^(d+2) : ℝ)
        (G.subgroupDisplacementBall Λ o (2*n)) := by
  obtain ⟨Λ,hΛ,horbit,hreps⟩ := G.finitelyGenerated_quasiTransitive_subgroup hc hl hq o
  refine ⟨Λ,hΛ,horbit,hreps,?_⟩
  intro R
  obtain ⟨n,hn,hd⟩ := G.orbitBall_doubling_scales hc hl hq o d hpoly R
  refine ⟨n,hn,?_⟩
  exact_mod_cast G.subgroupDisplacementBall_approximate hl o n (5^(d+2)) Λ horbit hd

theorem main_failure_finitelyGenerated_model [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1)
    (hper : G.law G.criticalProbability G.percolates≠0) (o : V) :
    ∃ d : ℕ, 2≤d ∧ ∃ Λ : Subgroup G.Aut, Group.FG Λ ∧
      MulAction.orbit Λ o=MulAction.orbit G.Aut o ∧
      (∃ S : Set V, S.Finite ∧ ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) ∧
      ∀ R : ℕ, ∃ n≥R, IsApproximateSubgroup (5^(d+2) : ℝ)
        (G.subgroupDisplacementBall Λ o (2*n)) := by
  obtain ⟨_,_,d,hd,hpoly⟩ := G.main_failure_sparse_polynomial hc hl hq hpc hper
  exact ⟨d,hd,G.sparse_polynomial_finitelyGenerated_model hc hl hq o d hpoly⟩

end CriticalPercolation.BondGraph
end
end

end OAI
